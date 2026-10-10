-- Prove2me | Theorems.Thm_PriceQualityService_Surplus_equation_17
-- name    : PriceQualityService.Surplus.equation_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:19:07.620425+00:00
-- url     : https://prove2.me/theorems/bd9df6b8-c4a0-4ac8-b3bf-30fc78d987c4
-- title:
--   Equation (17): the price-only MNL optimum has equal markups $1+r^\dagger$ and profit $r^\dagger$
-- statement:
--   Fix qualities $\mathbf q\in\mathbb R^N$ and service durations $\mathbf t\in\mathbb R^N$, and consider the firm's price-only problem $\max_{\mathbf p}\Pi(\mathbf p,\mathbf q,\mathbf t;\mathcal N)$ under the MNL model. Then:
--
--   1. the equation in $r$
--   $$
--   r=\sum_{i\in\mathcal N}\exp\big(\alpha_iq_i-c_iq_i^2+t_i(s_i-(a_i-b_iq_i))-r-1\big)\qquad(17)
--   $$
--   has exactly one real solution $r^\dagger$;
--   2. a price vector $\mathbf p$ maximizes $\Pi(\cdot,\mathbf q,\mathbf t;\mathcal N)$ if and only if
--   $$
--   p_i=1+r^\dagger+c_iq_i^2+t_i(a_i-b_iq_i)\quad\text{for every } i\in\mathcal N,
--   $$
--   that is, every product carries the same markup $1+r^\dagger$;
--   3. the maximal profit is $r^\dagger$.
--
--   This is the price step of the proof of Theorem 1, and it supplies the price-only benchmark $r^\dagger$ and the optimal prices $\mathbf p^\dagger$ in the proof of Proposition 5.
--
--   **Formalization Note** No sign or range condition on the parameters is needed: the qualities and durations are fixed, so $c_iq_i^2$ and $t_i(a_i-b_iq_i)$ are constants.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), p. 26 (PDF p. 26), eq. (17) in the proof of Theorem 1; Online Supplement p. 1 (PDF p. 34), proof of Proposition 5

import Mathlib
import Definitions.Def_PriceQualityService_Surplus_Problems

namespace PriceQualityService.Surplus

open Finset

/-- Equation (17), Wang, Ke & Cui, accepted manuscript (SSRN 3766191), p. 26 (proof of
Theorem 1; used as the price-only optimum in the proof of Proposition 5, Online Supplement p. 1).
For fixed qualities `q` and service durations `t`, the equation
`r = ∑_i exp(α_i q_i − c_i q_i² + t_i(s_i − (a_i − b_i q_i)) − r − 1)` has a unique real root
`r†`; a price vector maximizes `Π(·, q, t; 𝒩)` if and only if every price equals
`1 + r† + c_i q_i² + t_i(a_i − b_i q_i)`; and the maximal profit is `r†`. -/
theorem equation_17 {N : ℕ} (α a b c s : Fin N → ℝ) (q t : Fin N → ℝ) :
    ∃ r : ℝ,
      r = ∑ i, Real.exp (α i * q i - c i * q i ^ 2 + t i * (s i - (a i - b i * q i)) - r - 1) ∧
      (∀ r' : ℝ,
        r' = ∑ i, Real.exp (α i * q i - c i * q i ^ 2 + t i * (s i - (a i - b i * q i)) - r' - 1) →
          r' = r) ∧
      (∀ p : Fin N → ℝ, IsPriceOptimal α a b c s q t p ↔
        ∀ i, p i = 1 + r + c i * q i ^ 2 + t i * (a i - b i * q i)) ∧
      (∀ p : Fin N → ℝ, IsPriceOptimal α a b c s q t p → PriceQualityService.Joint.profit α a b c s p q t = r) := by sorry

end PriceQualityService.Surplus
