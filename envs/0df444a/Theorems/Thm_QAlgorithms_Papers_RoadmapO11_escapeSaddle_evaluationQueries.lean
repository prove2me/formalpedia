-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapO11_escapeSaddle_evaluationQueries
-- name    : QAlgorithms.Papers.RoadmapO11.escapeSaddle_evaluationQueries
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T18:48:30.665381+00:00
-- url     : https://prove2.me/theorems/21e28871-1297-443b-a714-5b7b1714fdfa
-- title:
--   Escape from saddle points using quantum evaluation queries
-- statement:
--   Fix positive smoothness bounds $\ell,\rho$, confidence $0<\delta<1$, and a nonnegative starting gap $\Delta$. Let $f:\mathbb R^n\to\mathbb R$ be twice differentiable, with globally $\ell$-Lipschitz gradient in Euclidean norm and globally $\rho$-Lipschitz Hessian in operator norm. Assume $f$ attains its finite global minimum $f^*$, and let the public initial point $x_0$ satisfy $f(x_0)-f^*=\Delta$. For $0<\varepsilon\le\ell^2/\rho$, set $g=\Delta(\log n)^2\varepsilon^{-7/4}$.
--
--   There are $C>0$, a nonnegative integer $a$, and thresholds $n_0\ge2$, $g_0\ge1$, depending only on the fixed public parameters. In the regime $n\ge n_0$ and $g\ge g_0$, a quantum evaluation-query program can be chosen using $n,\varepsilon,x_0$ and those public parameters before $f$ and its oracle. For every coherent value-output unitary satisfying $U_f|x,0,0\rangle=|x,f(x),0\rangle$, its joint output and evaluation-call law obeys
--
--   $$
--   \Pr\!\left[\|\nabla f(x)\|_2\le\varepsilon,\quad\lambda_{\min}(\nabla^2f(x))\ge-\sqrt{\rho\varepsilon},\quad Q\le Cg\max\{1,\log g\}^{a}\right]\ge1-\delta.
--   $$
--
--   Here $Q$ counts forward and inverse evaluation-oracle applications. There are no free gradient, Hessian or simulation queries. If $\Delta=0$, the program returns $x_0$ without queries, including in dimension one. Positive-gap small dimensions and scales are outside this asymptotic statement.
--
--   This is the authors' ideal-oracle existence claim, with the displayed $\log^2 n$ and $\varepsilon^{-7/4}$ dependence and their broad convention $\widetilde O(g)=O(g\,\mathrm{poly}(\log g))$. The formal counterpart combines Theorem 4, Eq. (66), pages 18–19, Remark 2 on page 20, and the accelerated evaluation-only extension asserted after Theorem 5 and in Remark 3 on page 24. It does not assert an exact local minimum or correctness of a specific finite-accuracy implementation.
--
--   **Formalization Note** The frozen ideal real-label register and adaptive evaluation-program semantics provide the joint law. The Hessian lower bound is its equivalent quadratic-form inequality on every real vector. Measurability is concluded for the chosen program, and the gap is computed from an attained minimum. The action of the oracle on dirty value registers is left unrestricted.
-- source:
--   Quantum algorithms for escaping from saddle points, arXiv:2007.10253v3, Theorem 1 (Main result, informal), PDF p. 4. https://arxiv.org/abs/2007.10253v3 . PDF SHA-256: 58376b0bc95152eebb7059cd474c4b1d076fddd79427a8eedb6b06600ce945e7.

import Definitions.Def_QAlgorithms_Defs_NonconvexQueryContracts
set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace QAlgorithms.Papers.RoadmapO11

open QAlgorithms.Nonconvex

/-- Zhang, Leng, Li, arXiv:2007.10253v3, Theorem 1 (informal), PDF p.4.
The original-paper existence claim is made explicit by Theorem 4, Eq.(66),
pp.18-19, the returned-point rule of Remark 2, p.20, and the accelerated
evaluation-only extension asserted after Theorem 5 and in Remark 3, p.24.
Smoothness and stationarity are those of p.2, Eq.(1); access is precisely
the clean real-value unitary interface of p.3, Eqs.(2)-(3). All oracle calls,
including inverse calls, are counted by the computed execution law.

The actual attained starting gap is public. Smoothness, confidence and gap
are fixed before the asymptotic constants; the program and its normalized
reset/start state are chosen before the objective and every compatible
oracle completion. The successful returned-point and cost event has mass
at least 1-delta. The p.1 footnote's broad poly(log(scale)) convention is
used, retaining the displayed log(n)^2 and epsilon^(-7/4) factors.
The zero-gap branch returns x0 without queries; positive-gap dimensions
and scales are asymptotic, avoiding a zero-query claim from log(1)=0.

This states the authors' ideal-oracle existence claim, not correctness of
literal Algorithm 3, a corrected construction, or an accelerated finite-
accuracy guarantee. The printed perturbation length, failure allocation,
unsquared trigger and continuum/periodic error issues are recorded in the
unit's SOURCE_AUDIT.md; no source correction is applied here. -/
theorem escapeSaddle_evaluationQueries
    (ell rho delta gap : ℝ) (hell : 0 < ell) (hrho : 0 < rho)
    (hdelta : 0 < delta ∧ delta < 1) (hgap : 0 ≤ gap) :
    ∃ C : ℝ, 0 < C ∧ ∃ degree : ℕ, ∃ n0 : ℕ, 2 ≤ n0 ∧
      ∃ threshold : ℝ, 1 ≤ threshold ∧
      ∀ (n : ℕ) (eps : ℝ), 1 ≤ n → 0 < eps → eps ≤ ell ^ 2 / rho →
        let scale : ℝ := gap * (Real.log n) ^ 2 * eps ^ (-(7 / 4 : ℝ))
        (gap = 0 ∨ (n0 ≤ n ∧ threshold ≤ scale)) →
        ∀ x0 : Vector n,
          ∃ (w : ℕ) (zero : Register n (Fin (w + 1))) (zero_unit : ‖zero‖ = 1)
            (program : EvaluationProgram n (Fin (w + 1))),
            (gap = 0 → program = .output x0) ∧
            ∀ f : Vector n → ℝ, IsSmoothHessianLipschitz f ell rho →
            ∀ attained : ∃ x, ∀ y, f x ≤ f y,
              initialGap f attained x0 = gap →
              ∀ U : Register n (Fin (w + 1)) ≃ₗᵢ[ℂ] Register n (Fin (w + 1)),
                IsRealEvaluationOracle (0 : Fin (w + 1)) U f →
                ∃ measurable : IsEvaluationProgramMeasurable zero zero_unit U program,
                  evaluationExecutionLaw zero zero_unit U program zero zero_unit measurable
                    {xq | IsApproxSecondOrderStationary f rho eps xq.1 ∧
                      (xq.2 : ℝ) ≤ if gap = 0 then 0
                        else C * scale * max 1 (Real.log scale) ^ degree} ≥
                    ENNReal.ofReal (1 - delta) := by sorry

end QAlgorithms.Papers.RoadmapO11
