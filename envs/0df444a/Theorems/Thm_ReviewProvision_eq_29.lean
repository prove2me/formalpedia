-- Prove2me | Theorems.Thm_ReviewProvision_eq_29
-- name    : ReviewProvision.eq_29
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:58:03.812347+00:00
-- url     : https://prove2.me/theorems/18dfd447-7257-460d-ad2b-cf307ef2920d
-- title:
--   Eq. (29), p.45 — $k^*_F$ is the unique solution
-- statement:
--   Let $N\ge2$, and for $k>0$ write $w=k\theta\zeta$ and $\sigma_F^2=\sigma^2(w)$ for the symmetric variance. The equation
--
--   $$
--   k=\frac12+\frac{m\theta\zeta}{8}\,g(\sigma_F)\,\frac{\partial\sigma_F^2}{\partial w_F}
--   $$
--
--   has exactly one solution $k>0$, and if $(k_0,\dots,k_0)$ is optimal for FP then $k_0>0$ is that solution. Here, for every $w\ge0$,
--
--   $$
--   \frac{\partial\sigma_F^2}{\partial w_F}=\frac{N\eta^2[Nw^2+\eta(2w+\eta)]+2\tau\eta(w+\eta)(Nw+\eta)+\tau^2(w+\eta)^2}{(w+\eta)^2[Nw\eta+(w+\eta)\tau]^2}>0
--   $$
--
--   is the derivative of $\sigma^2$.
--
--   This pins the optimal symmetric sales down by a single equation.
--
--   Differences from the source:
--   - encoding: the solution of (29), k_F unrestricted → 0 < k; reason: g needs σ > 0, and k = 0 is not an optimum (eq_27)
--   - reading: the denominator printed (w+η)²[Nwη+(w+η)τ]2 with a final 2 on the line → the exponent 2; reason: the final 2 is an exponent; checked against the derivative of the closed form
--   - reading: the feasible sales are not stated → k_n ≥ 0 for all n, with no upper bound; reason: the proofs use k_N ≥ 0 and evaluate at k_N = 0 (pp.37, 44); (27) has no multiplier, and an upper bound k_n ≤ 1 is not intended since the optimum can exceed 1
-- source:
--   Xiao, Chen, Tang, Customer Review Provision Policies with Heterogeneous Cluster Preferences, SSRN 3403322 (manuscript of 2021-05-24), eq. (29), p.45

import Mathlib
import Definitions.Def_ReviewProvision_IsOptimal
import Definitions.Def_ReviewProvision_closedForms
import Definitions.Def_ReviewProvision_truncatedMoments

open MeasureTheory ProbabilityTheory

namespace ReviewProvision

/-- **Eq. (29)**, SSRN 3403322 (manuscript of 2021-05-24), p.45 (PDF 45): the equation
`k = 1/2 + (mθζ/8) g(σ_F) ∂σ²_F/∂w_F`, with `w = k θ ζ` and `σ_F² = sigmaSqSym p N w`, has exactly one
solution `k > 0`, and a symmetric optimum of FP is a solution. `dSigmaSqSym` (the display below (29)) is
the derivative of `sigmaSqSym` and is positive.

**Formalization Note.** The set is `k > 0` because `g` needs `σ > 0`, and `k = 0` is not an optimum
(`eq_27`). -/
theorem eq_29 (p : Params) {N : ℕ} (hN : 2 ≤ N) :
    (∃! k : ℝ, 0 < k ∧
      k = 1 / 2 + p.m * p.theta * p.zeta / 8 *
        g √(sigmaSqSym p N (k * p.theta * p.zeta)) *
        dSigmaSqSym p N (k * p.theta * p.zeta)) ∧
    (∀ k₀ : ℝ, IsOptimal p .FP (fun _ : Fin N => k₀) →
      0 < k₀ ∧
      k₀ = 1 / 2 + p.m * p.theta * p.zeta / 8 *
        g √(sigmaSqSym p N (k₀ * p.theta * p.zeta)) *
        dSigmaSqSym p N (k₀ * p.theta * p.zeta)) ∧
    ∀ w : ℝ, 0 ≤ w →
      HasDerivAt (sigmaSqSym p N) (dSigmaSqSym p N w) w ∧ 0 < dSigmaSqSym p N w := by sorry

end ReviewProvision
