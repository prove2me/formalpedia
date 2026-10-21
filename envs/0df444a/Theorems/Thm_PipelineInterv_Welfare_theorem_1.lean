-- Prove2me | Theorems.Thm_PipelineInterv_Welfare_theorem_1
-- name    : PipelineInterv.Welfare.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:23:21.264626+00:00
-- url     : https://prove2.me/theorems/f8b7b22d-04c1-4b01-8b7f-fffee767fefb
-- title:
--   Theorem 1, p. 10 — every run of Algorithm 1 is budget-feasible with welfare ≥ OPT − 3(k−1)ε‖R‖∞; LP-instance count (corrected)
-- statement:
--   Fix an instance of the pipeline intervention problem with $k$ layers of width $w$ satisfying the standing assumptions of §2 (left stochastic $M^0_t$, a distribution $D_1$, rewards $R\ge0$), a budget $B\ge0$, a discretization parameter $\varepsilon>0$, and any finite $\varepsilon$-net $\mathcal D(\varepsilon)\subseteq\mathcal D$ of the simplex in $\ell_1$. Then:
--
--   1. **(existence)** Algorithm 1 has a run, i.e. every Program (7) and every selection step it performs has a maximizer;
--   2. **(guarantee)** for every run, the returned tuple $M(B^\varepsilon,D_1)=(M_1,\dots,M_{k-1})$ lies in $\mathcal F(B,M^0_1,\dots,M^0_{k-1})$, and for every $(M'_1,\dots,M'_{k-1})\in\mathcal F(B,M^0_1,\dots,M^0_{k-1})$
--   $$W(M_1,\dots,M_{k-1})\ \ge\ W(M'_1,\dots,M'_{k-1})-3(k-1)\,\varepsilon\,\|R\|_\infty ,$$
--   that is, the algorithm achieves social welfare at least $OPT-3(k-1)\varepsilon\|R\|_\infty$;
--   3. **(running time, corrected)** the number of instances of Program (7) the algorithm solves is at most
--   $$(k-1)\,\bigl(\lfloor B/\varepsilon\rfloor+1\bigr)^2\,|\mathcal D(\varepsilon)|^2 .$$
--
--   With the net of Claim 2 and a polynomial-time LP solver for Program (7), this gives an algorithm whose running time is polynomial in $k$, $B/\varepsilon$ and $1/\varepsilon$ for every fixed width $w$, with additive welfare loss $3(k-1)\varepsilon\|R\|_\infty$.
--
--   **Formalization Note.** $OPT$, the maximum of Program (1), is replaced by "every feasible tuple", equivalent by Remark 3 (p. 7). A run of Algorithm 1 may break ties arbitrarily, and the guarantee is stated for every run and every net. Transitions are 0-based (`Fin K`, $K=k-1$). The page states the running time as $O\bigl(k\,\tfrac{B}{\varepsilon}(\tfrac1\varepsilon)^{w^2}f(w)\bigr)$; its proof (p. 13) counts one Program (7) per budget split of $B_{\ge t}$ and per pair of net points but does not multiply by the number of values of $B_{\ge t}$, so clause 3 states the corrected count of LP instances, $(k-1)(\lfloor B/\varepsilon\rfloor+1)^2|\mathcal D(\varepsilon)|^2$, rather than an asymptotic time bound.
-- source:
--   Arunachaleswaran, Kannan, Roth, Ziani, Pipeline Interventions, arXiv:2002.06592v2, p. 10, Theorem 1 (proof pp. 11–13); running-time clause corrected to an LP-instance count

import Mathlib
import Definitions.Def_PipelineInterv_Welfare_Model

namespace PipelineInterv.Welfare
open Matrix

theorem theorem_1 {w K : ℕ} (I : Instance w K) (hI : I.Standing) (B ε : ℝ) (hB : 0 ≤ B)
    (hε : 0 < ε) (S : Finset (Fin w → ℝ)) (hS : IsEpsNet ε S) :
    (∃ tab : Table w K, IsAlg1Run I B ε S tab) ∧
    (∀ tab : Table w K, IsAlg1Run I B ε S tab →
      Feasible I B (alg1Output I B ε tab) ∧
      ∀ M, Feasible I B M →
        welfare I M - 3 * (K : ℝ) * ε * supNorm I.R ≤ welfare I (alg1Output I B ε tab)) ∧
    alg1LPCount I B ε S ≤ K * (⌊B / ε⌋₊ + 1) ^ 2 * S.card ^ 2 := by sorry

end PipelineInterv.Welfare
