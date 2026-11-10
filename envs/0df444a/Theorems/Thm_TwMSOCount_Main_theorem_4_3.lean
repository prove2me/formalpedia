-- Prove2me | Theorems.Thm_TwMSOCount_Main_theorem_4_3
-- name    : TwMSOCount.Main.theorem_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:46:34.063516+00:00
-- url     : https://prove2.me/theorems/39e8c4c6-acf1-47bc-a340-36992c23106b
-- title:
--   Theorem 4.3 — exact table values: each graph has exactly one expanded description, of weight its partial weight; the algorithm returns $Z_{k,n}(\psi)$
-- statement:
--   Fix $\theta=(k,C,\psi)$, weights, and a state map (Definition 4.1). Let $G$, $U$ be the tables defined by the recurrences (3)–(8).
--
--   **Theorem.** A solution of the recurrences exists, and every expanded description outputs a graph of its defining class. Every table entry equals the total partial weight of the graphs in its defining class (Definition B.3):
--   $$G_B(m,\tau)=\sum_{H\in\mathcal G_B(m,\tau)}W_B(H),\qquad U_\gamma(I,m,\tau)=\sum_{K\in\mathcal U_\gamma(I,m,\tau)}W_{J\cup I}(K).$$
--   More strongly, each graph of a defining class (on the internal labels $\{0,\dots,m-1\}$) is the output of exactly one expanded description (Definition B.4) of its entry, and the local factors of this description multiply to its partial weight. In particular, the algorithm returns
--   $$\sum_{\tau\in T_\emptyset:\ \mathrm{acc}(\tau)} G_\emptyset(n,\tau) = Z_{k,n}(\psi).$$
--
--   This is the correctness of the counting algorithm for any state map; Proposition 5.1 supplies one.
--
--   Differences from the source:
--   - encoding: a state map (Definition 4.1); the test Φ_{B,B_S,N} → StateMap with IsStateMap ψ (states coded by ℕ, finite sets T_B); Φ_{B,B_S,N} by its meaning PhiT from Appendix C.2; reason: Appendix C.2 gives the truth of Φ on every structure as First_{B,P} ∧ Sel_{B,P,N}; the computability of the bounds on |T_B| is meaningful only uniformly in θ and is the content of Proposition 5.1
--   - encoding: the tables computed by the recurrences → any tab : Entry → ℚ≥0 with SolvesRecurrences (equations (3)–(8) at every existing entry); reason: Proposition 4.2 makes the solution unique, so this is the computed table
--   - encoding: each such graph is the output of exactly one expanded description → ∃! d : ExpDesc SM e (range m) with IsoOut d.output H, and every such d has d.weight = W(H); reason: outputs are built by gluing on new vertex types, so 'is the output' is an isomorphism preserving colors, boundary labels and output labels
--   - encoding: acc(τ) → StateMap.Acc ψ τ: a graph of state τ ∈ T_∅ satisfies ψ; reason: by Definition 4.1(iii) all graphs of the state agree on ψ
--   - encoding: the algorithm computes the tables and expanded descriptions form a weight-preserving bijection onto the defining classes (B.5) → existence of a solution of the recurrences, validity of every expanded-description output, unique preimages, weight preservation, and the exact root sum; reason: states the complete construction and both directions of the bijection, including zero-weight outputs
-- source:
--   Zou, Wang, Chang, Wang, Kuželka, Exact Counting and Sampling of Labeled Graphs of Bounded Treewidth with MSO Properties, STOC 2027 submission (manuscript sha256 2715a74f…775b), Theorem 4.3, p. 11 (PDF 12); proof in Appendix B.5, pp. 21–23 (PDF 22–24)

import Mathlib
import Definitions.Def_PlantedSubgraphLD_tw
import Definitions.Def_TwMSOCount_Main_MSO2
import Definitions.Def_TwMSOCount_Main_Weights
import Definitions.Def_TwMSOCount_Main_BGraph
import Definitions.Def_TwMSOCount_Main_Separator
import Definitions.Def_TwMSOCount_Main_Tables

open Classical

namespace TwMSOCount.Main

theorem theorem_4_3 {r k : ℕ} [NeZero r] (ψ : Formula r Empty) (hψ : ψ.IsSentence)
    (w : Weights r) (SM : StateMap r k) (hSM : SM.IsStateMap ψ) :
    (∃ tab : Entry r k → ℚ≥0, SolvesRecurrences SM w tab) ∧
    (∀ tab : Entry r k → ℚ≥0, SolvesRecurrences SM w tab →
      ∀ e : Entry r k, e.Valid SM → tab e = classSum SM w e) ∧
    (∀ (B : Finset (Lab k)) (m τ : ℕ), (Entry.g B m τ).Valid SM →
      ∀ d : ExpDesc SM (.g B m τ) (Finset.range m),
        ∃ (G : SimpleGraph (B ⊕ Fin m)) (χ : B ⊕ Fin m → Fin r),
          (BGraph.stored B m G χ).tw ≤ k ∧ SM.st (BGraph.stored B m G χ) = τ ∧
          BGraph.IsoOut d.output (BGraph.stored B m G χ)) ∧
    (∀ (γ : Ctx r k) (I : Finset (Lab k)) (m τ : ℕ), (Entry.u γ I m τ).Valid SM →
      ∀ d : ExpDesc SM (.u γ I m τ) (Finset.range m),
        ∃ (G : SimpleGraph ((γ.J ∪ I : Finset (Lab k)) ⊕ Fin m))
          (χ : (γ.J ∪ I : Finset (Lab k)) ⊕ Fin m → Fin r),
          IsCollection γ I (BGraph.stored (γ.J ∪ I) m G χ) ∧
          SM.st (BGraph.stored (γ.J ∪ I) m G χ) = τ ∧
          BGraph.IsoOut d.output (BGraph.stored (γ.J ∪ I) m G χ)) ∧
    (∀ (B : Finset (Lab k)) (m τ : ℕ), (Entry.g B m τ).Valid SM →
      ∀ (G : SimpleGraph (B ⊕ Fin m)) (χ : B ⊕ Fin m → Fin r),
        (BGraph.stored B m G χ).tw ≤ k → SM.st (BGraph.stored B m G χ) = τ →
        (∃! d : ExpDesc SM (.g B m τ) (Finset.range m),
          BGraph.IsoOut d.output (BGraph.stored B m G χ)) ∧
        ∀ d : ExpDesc SM (.g B m τ) (Finset.range m),
          BGraph.IsoOut d.output (BGraph.stored B m G χ) →
            d.weight w = BGraph.pw w (BGraph.stored B m G χ)) ∧
    (∀ (γ : Ctx r k) (I : Finset (Lab k)) (m τ : ℕ), (Entry.u γ I m τ).Valid SM →
      ∀ (G : SimpleGraph ((γ.J ∪ I : Finset (Lab k)) ⊕ Fin m))
        (χ : (γ.J ∪ I : Finset (Lab k)) ⊕ Fin m → Fin r),
        IsCollection γ I (BGraph.stored (γ.J ∪ I) m G χ) →
        SM.st (BGraph.stored (γ.J ∪ I) m G χ) = τ →
        (∃! d : ExpDesc SM (.u γ I m τ) (Finset.range m),
          BGraph.IsoOut d.output (BGraph.stored (γ.J ∪ I) m G χ)) ∧
        ∀ d : ExpDesc SM (.u γ I m τ) (Finset.range m),
          BGraph.IsoOut d.output (BGraph.stored (γ.J ∪ I) m G χ) →
            d.weight w = BGraph.pw w (BGraph.stored (γ.J ∪ I) m G χ)) ∧
    (∀ tab : Entry r k → ℚ≥0, SolvesRecurrences SM w tab → ∀ n : ℕ,
      ∑ τ ∈ (SM.states ∅).filter (SM.Acc ψ), tab (.g ∅ n τ) = Z k n r ψ w) := by sorry

end TwMSOCount.Main
