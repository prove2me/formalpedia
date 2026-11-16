-- Prove2me | Theorems.Thm_TwoConnSS_Supplement_theorem_5_3
-- name    : TwoConnSS.Supplement.theorem_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:46:43.714853+00:00
-- url     : https://prove2.me/theorems/bdfbe0e0-c40f-4cc9-a53c-a09effaf2f46
-- title:
--   Theorem 5.3 — 2ECSS within $(11/9)\mu+1/144+\varepsilon$ from a $\mu$-approximation for $\{3,4\}$-cycle-free 2-edge-covers
-- statement:
--   Write $\mathrm{opt}_E(G)$ for the minimum number of edges of a 2-edge-connected spanning subgraph of a 2-edge-connected graph $G$. Suppose that, for a real $\mu\ge1$, there is a polynomial-time $\mu$-approximation algorithm for minimum $\{3,4\}$-cycle-free 2-edge-cover in 2-edge-connected graphs (the hypothesis $\mathrm{CoverApprox}(\mu)$).
--
--   1. For every fixed $\varepsilon>0$ there is a polynomial-time algorithm that, on every 2-edge-connected graph $G$, returns a 2-edge-connected spanning subgraph $F\subseteq E(G)$ with
--   $$
--   |F|\le\Bigl(\frac{11}{9}\mu+\frac{1}{144}+\varepsilon\Bigr)\mathrm{opt}_E(G).
--   $$
--   2. If there is a PTAS for minimum $\{3,4\}$-cycle-free 2-edge-cover in 2-edge-connected graphs, i.e. $\mathrm{CoverApprox}(1+\delta)$ holds for every $\delta>0$, then for every fixed $\varepsilon>0$ there is a polynomial-time $(59/48+\varepsilon)$-approximation for 2ECSS; in particular, since $59/48<1.23$, there is a polynomial-time $r$-approximation for 2ECSS with some $r<1.23$.
--
--   So any progress on the $\{3,4\}$-cycle-free cover problem transfers to 2ECSS, and a PTAS for it would push the 2ECSS ratio below $1.23$.
--
--   **Formalization Note** Machines are `Turing.TM2ComputableInPolyTime` on `encIn`/`encOut`, one per fixed $\varepsilon$ (and in the hypothesis one per fixed $\mu$ or $\delta$). The optimum is written as "for every 2ECSS $F'$ of $G$". The hypothesis `CoverApprox` requires the cover algorithm only on 2EC graphs that admit a $\{3,4\}$-cycle-free 2-edge-cover (see that definition).
--
--   Differences from the source:
--   - reading: a $\mu$-approximation for the cover problem "in 2-edge-connected graphs" → required only on 2EC graphs that admit a $\{3,4\}$-cycle-free 2-edge-cover; reason: the triangle and the 4-cycle are 2EC with no such cover, so the literal reading makes the hypothesis unsatisfiable and the theorem vacuous; this reading is the weaker hypothesis, hence the stronger theorem.
--   - reading: "yields a $(59/48+\varepsilon<1.23)$-approximation, for $\varepsilon$ small enough" → for every $\varepsilon>0$ a $(59/48+\varepsilon)$-approximation, and some ratio $r<123/100$; reason: both readings of the sentence are stated.
--   - encoding: polynomial-time algorithm, no machine model named → `Turing.TM2ComputableInPolyTime` on `encIn`/`encOut`; reason: Lean convention shared with the base Theorem 5.1.
--   - encoding: $\mathrm{opt}_E(G)$ → every 2ECSS $F'$ of $G$; reason: the optimum is attained; equivalent.
-- source:
--   A. Jabal Ameli, Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning Subgraphs, STOC 2027 submission (manuscript sha256 22d0f2a895e1fa238a27dca51f52b9f9f0c99a02bea4adcddcacca2e27e2ae6a), Theorem 5.3, p.20 (PDF 21); restates Theorem 1.3, p.2; proof §8.4, p.72 (PDF 73)

import Mathlib
import Definitions.Def_TwoConnSS_Inst
import Definitions.Def_TwoConnSS_IsTwoECSS
import Definitions.Def_TwoConnSS_encIn
import Definitions.Def_TwoConnSS_Supplement_CoverApprox

namespace TwoConnSS.Supplement

open TwoConnSS

/-- **Theorem 5.3 (= Theorem 1.3): 2ECSS from an approximation for {3, 4}-cycle-free
2-edge-covers.**
Jabal Ameli, *Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning
Subgraphs*, STOC 2027 submission (manuscript sha256 22d0f2a8…), Theorem 5.3, p.20 (restating
Theorem 1.3, p.2); proof §8.4, p.72: "Suppose there is a polynomial-time μ-approximation algorithm
for minimum {3, 4}-cycle-free 2-edge-cover in 2-edge-connected graphs, where μ ≥ 1. For every fixed
ε > 0, there is a polynomial-time (11/9 · μ + 1/144 + ε)-approximation for 2ECSS. In particular, a
PTAS for minimum {3, 4}-cycle-free 2-edge-cover yields a (59/48 + ε < 1.23)-approximation, for ε
small enough."

1. If `μ ≥ 1` and `CoverApprox μ` holds, then for every real `ε > 0` there is a polynomial-time
   `alg` that on every 2EC instance `G` outputs a 2ECSS `F` with
   `|F| ≤ ((11/9)·μ + 1/144 + ε)·|F'|` for every 2ECSS `F'` of `G`.
2. If `CoverApprox (1 + δ)` holds for every `δ > 0` (a PTAS), then for every `ε > 0` there is a
   polynomial-time `(59/48 + ε)`-approximation for 2ECSS, and there is a polynomial-time
   `r`-approximation for 2ECSS with some `r < 1.23`.

**Formalization Note.** Machines are `Turing.TM2ComputableInPolyTime` on `encIn`/`encOut`, one per
fixed `ε` (and, in the hypothesis, per fixed `μ` or `δ`). "For ε small enough" is the existential
`r < 123/100`. OPT is "every feasible `F'`". -/
theorem theorem_5_3 :
    (∀ μ : ℝ, 1 ≤ μ → CoverApprox μ →
      ∀ ε : ℝ, 0 < ε → ∃ alg : Inst → List (ℕ × ℕ),
        Nonempty (Turing.TM2ComputableInPolyTime encIn encOut alg) ∧
        ∀ I : Inst, IsTwoEC I.graph →
          IsTwoECSS I.graph (toEdges I.n (alg I)) ∧
          ∀ F' : Finset (Sym2 (Fin I.n)), IsTwoECSS I.graph F' →
            ((toEdges I.n (alg I)).card : ℝ) ≤ (11 / 9 * μ + 1 / 144 + ε) * (F'.card : ℝ)) ∧
    ((∀ δ : ℝ, 0 < δ → CoverApprox (1 + δ)) →
      (∀ ε : ℝ, 0 < ε → ∃ alg : Inst → List (ℕ × ℕ),
        Nonempty (Turing.TM2ComputableInPolyTime encIn encOut alg) ∧
        ∀ I : Inst, IsTwoEC I.graph →
          IsTwoECSS I.graph (toEdges I.n (alg I)) ∧
          ∀ F' : Finset (Sym2 (Fin I.n)), IsTwoECSS I.graph F' →
            ((toEdges I.n (alg I)).card : ℝ) ≤ (59 / 48 + ε) * (F'.card : ℝ)) ∧
      ∃ r : ℝ, r < 123 / 100 ∧ ∃ alg : Inst → List (ℕ × ℕ),
        Nonempty (Turing.TM2ComputableInPolyTime encIn encOut alg) ∧
        ∀ I : Inst, IsTwoEC I.graph →
          IsTwoECSS I.graph (toEdges I.n (alg I)) ∧
          ∀ F' : Finset (Sym2 (Fin I.n)), IsTwoECSS I.graph F' →
            ((toEdges I.n (alg I)).card : ℝ) ≤ r * (F'.card : ℝ)) := by sorry

end TwoConnSS.Supplement
