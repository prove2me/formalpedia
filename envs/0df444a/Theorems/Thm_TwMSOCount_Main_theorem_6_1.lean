-- Prove2me | Theorems.Thm_TwMSOCount_Main_theorem_6_1
-- name    : TwMSOCount.Main.theorem_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:46:53.9116+00:00
-- url     : https://prove2.me/theorems/d3a11a30-d6c3-44e5-9ceb-824eface405e
-- title:
--   Theorem 6.1 — the recursive sampler outputs each $(H,\chi)$ with probability $W(H,\chi)/Z_{k,n}(\psi)$
-- statement:
--   Fix $\theta$, weights and a state map, and let $G$, $U$ be the tables of the recurrences (3)–(8). The **recursive sampler** (Algorithm 2) chooses an accepting root state $\tau$ with probability $G_\emptyset(n,\tau)/\sum_{\mathrm{acc}}G_\emptyset(n,\cdot)$ and samples from its graph entry: at a positive entry $Z = \sum_b w_b\prod_i Z_{b,i}$ it selects the summand $b$ with probability $w_b\prod_i Z_{b,i}/Z$, allocates its output labels uniformly among the allocations counted by its binomial coefficient, and samples the children independently on their label sets. A run of the sampler is an expanded description of the root entry on $\{0,\dots,n-1\}$; its probability is the product of these choice probabilities.
--
--   **Theorem.** If $Z_{k,n}(\psi)>0$, this procedure outputs each colored labeled graph $(H,\chi)$ on $[n]$ with $\mathrm{tw}(H)\le k$ and $(H,\chi)\models\psi$ with probability
--   $$\frac{W(H,\chi)}{Z_{k,n}(\psi)} .$$
--
--   Differences from the source:
--   - encoding: a state map (Definition 4.1); the test Φ_{B,B_S,N} → StateMap with IsStateMap ψ (states coded by ℕ, finite sets T_B); Φ_{B,B_S,N} by its meaning PhiT from Appendix C.2; reason: Appendix C.2 gives the truth of Φ on every structure as First_{B,P} ∧ Sel_{B,P,N}; the computability of the bounds on |T_B| is meaningful only uniformly in θ and is the content of Proposition 5.1
--   - encoding: the tables computed by the recurrences → any tab : Entry → ℚ≥0 with SolvesRecurrences (equations (3)–(8) at every existing entry); reason: Proposition 4.2 makes the solution unique, so this is the computed table
--   - encoding: vertex set [n] = {1,…,n} → Fin n = {0,…,n−1}; reason: relabeling i ↦ i−1 changes no instance
--   - encoding: the procedure outputs (H, χ) with probability … → Σ over accepting τ of (root choice probability) × Σ over expanded descriptions d of G_∅(n, τ) on range n whose output is IsoOut to (H, χ) of pathProb d; reason: Algorithm 2's runs are exactly the expanded descriptions, and pathProb is the product of its choice probabilities
-- source:
--   Zou, Wang, Chang, Wang, Kuželka, Exact Counting and Sampling of Labeled Graphs of Bounded Treewidth with MSO Properties, STOC 2027 submission (manuscript sha256 2715a74f…775b), Theorem 6.1, p. 12 (PDF 13); Algorithm 2 and proof in Appendix D.3, pp. 33–34 (PDF 34–35)

import Mathlib
import Definitions.Def_PlantedSubgraphLD_tw
import Definitions.Def_TwMSOCount_Main_MSO2
import Definitions.Def_TwMSOCount_Main_Weights
import Definitions.Def_TwMSOCount_Main_BGraph
import Definitions.Def_TwMSOCount_Main_Separator
import Definitions.Def_TwMSOCount_Main_Tables

open Classical
open scoped ENNReal NNReal

namespace TwMSOCount.Main

theorem theorem_6_1 {r k : ℕ} [NeZero r] (ψ : Formula r Empty) (hψ : ψ.IsSentence)
    (w : Weights r) (SM : StateMap r k) (hSM : SM.IsStateMap ψ) (tab : Entry r k → ℚ≥0)
    (htab : SolvesRecurrences SM w tab) (n : ℕ) (hZ : 0 < Z k n r ψ w)
    (G : SimpleGraph (Fin n)) (χ : Fin n → Fin r) (htw : PlantedSubgraphLD.tw G ≤ k)
    (hG : ModelsPsi G χ ψ) :
    (∑ τ ∈ (SM.states ∅).filter (SM.Acc ψ),
        (((tab (.g ∅ n τ) / ∑ τ' ∈ (SM.states ∅).filter (SM.Acc ψ), tab (.g ∅ n τ') : ℚ≥0)
          : ℝ≥0) : ℝ≥0∞) *
        ∑' d : ExpDesc SM (.g ∅ n τ) (Finset.range n),
          if BGraph.IsoOut d.output (rootGraph (k := k) G χ) then
            (((d.pathProb w tab : ℚ≥0) : ℝ≥0) : ℝ≥0∞) else 0) =
      (((w.W G χ / Z k n r ψ w : ℚ≥0) : ℝ≥0) : ℝ≥0∞) := by sorry

end TwMSOCount.Main
