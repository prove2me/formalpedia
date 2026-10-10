-- Prove2me | Theorems.Thm_TailRiskSharing_RobustVaR_proposition4_iii_robust_var
-- name    : TailRiskSharing.RobustVaR.proposition4_iii_robust_var
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T21:02:08.257108+00:00
-- url     : https://prove2.me/theorems/ff16eb6e-e895-4b89-97db-3e7bf44ce95e
-- title:
--   Proposition 4(iii), p. 30 — the Wasserstein-robust VaR solves (34), is the same for left and right VaR, and satisfies (35)
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be an atomless probability space, $X\in L^\infty$, $k\ge1$, $\delta>0$ and $\alpha\in(0,1)$. Write $[\rho]^k_\delta$ for the robust version of a risk measure $\rho$ over the order-$k$ Wasserstein ball of radius $\delta$. Then:
--
--   1. the suprema defining $[\mathrm{VaR}^L_\alpha]^k_\delta(X)$ and $[\mathrm{VaR}^R_\alpha]^k_\delta(X)$ are finite;
--   2. the equation in $x$
--
--   $$
--   \int_0^\alpha\big(x-\mathrm{VaR}^R_u(X)\big)_+^k\,\mathrm du=\delta^k
--   $$
--
--   has exactly one real solution;
--   3. that solution $x$ satisfies $[\mathrm{VaR}^L_\alpha]^k_\delta(X)=[\mathrm{VaR}^R_\alpha]^k_\delta(X)=x$;
--   4. moreover,
--
--   $$
--   [\mathrm{VaR}^R_\alpha]^k_\delta(X)\ge\mathrm{VaR}^R_\alpha(X)+\frac{\delta}{\alpha^{1/k}}.
--   $$
--
--   This gives a closed-form characterization of the worst-case Value-at-Risk under Wasserstein uncertainty and shows that the distinction between left and right VaR disappears after robustification.
--
--   **Formalization Note** Item 1 is implicit in the paper's claim that the supremum equals a real number $x$; it is stated explicitly because the robust measure is a real-valued `sSup`, which would return $0$ on an unbounded set. $k$ is a real number, as in the paper.
-- source:
--   Liu, Mao, Wang & Wei, Inf-convolution, Optimal Allocations, and Model Uncertainty for Tail Risk Measures, SSRN 3490348 (version of January 16, 2022), pp. 29–30, Proposition 4 (preamble and part (iii)), (34)–(35); proof p. 42

import Mathlib
import Definitions.Def_TailRiskSharing_RobustVaR_Setting
import Definitions.Def_TailRiskSharing_RobustVaR_Wasserstein

namespace TailRiskSharing.RobustVaR

open MeasureTheory

theorem proposition4_iii_robust_var {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hP : TailRiskSharing.VaRConv.IsAtomless P)
    (X : Ω → ℝ) (hX : X ∈ TailRiskSharing.TailConv.Linf P) (k δ α : ℝ) (hk : 1 ≤ k) (hδ : 0 < δ)
    (hα0 : 0 < α) (hα1 : α < 1) :
    BddAbove (robustSet P k δ (TailRiskSharing.VaRConv.VaRL P α) X) ∧ BddAbove (robustSet P k δ (TailRiskSharing.VaRConv.VaRR P α) X) ∧
    (∃! x : ℝ, ∫ u in (0:ℝ)..α, (max (x - TailRiskSharing.VaRConv.VaRR P u X) 0) ^ k = δ ^ k) ∧
    (∀ x : ℝ, ∫ u in (0:ℝ)..α, (max (x - TailRiskSharing.VaRConv.VaRR P u X) 0) ^ k = δ ^ k →
      robust P k δ (TailRiskSharing.VaRConv.VaRL P α) X = x ∧ robust P k δ (TailRiskSharing.VaRConv.VaRR P α) X = x) ∧
    TailRiskSharing.VaRConv.VaRR P α X + δ / α ^ (1 / k) ≤ robust P k δ (TailRiskSharing.VaRConv.VaRR P α) X := by sorry

end TailRiskSharing.RobustVaR
