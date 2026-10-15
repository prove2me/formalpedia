-- Prove2me | Theorems.Thm_StrictCompatLB_MeanField_theorem_4_11
-- name    : StrictCompatLB.MeanField.theorem_4_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:50:42.828435+00:00
-- url     : https://prove2.me/theorems/dc7beddc-ff70-4deb-9936-4108551dc860
-- title:
--   Theorem 4.11 — exponential global stability of the JSQ(d) mean-field ODE in a weighted ℓ¹ norm
-- statement:
--   Let $0<\lambda<1$ and $d\ge2$, and let $q^*(\infty)$ be the fixed point $q^*_i(\infty)=\lambda^{(d^i-1)/(d-1)}$ of
--   $$\frac{dq^*_i(t)}{dt}=\lambda\big(q^*_{i-1}(t)^d-q^*_i(t)^d\big)-\big(q^*_i(t)-q^*_{i+1}(t)\big),\qquad i=1,2,\dots\qquad(3.3)$$
--   For a positive sequence $\omega$ let $\Psi_\omega(t)=\sum_{i\ge1}\omega_i|q^*_i(t)-q^*_i(\infty)|$, and let $i_0=\min\{i\ge1:\lambda(2q^*_i(\infty)+1)<(1+\lambda)/2\}$. There is a positive sequence $\omega$ satisfying
--   $$\omega_{i_0+i}=\omega_{i_0}r^i\qquad\text{for }i\ge1\qquad(4.27)$$
--   for some $r\in(1,2/(1+\lambda))$, such that for every solution $q^*$ of (3.3) with values in $\mathcal Y$, if $\Psi_\omega(0)<\infty$ then $\Psi_\omega(t)$ converges exponentially to zero: $\Psi_\omega(t)\le c_0e^{-\delta t}$ for all $t\ge0$, for some $\delta>0$ and $c_0$.
--
--   Global stability of the limiting ODE in the same weighted norm in which the steady states are tight is what identifies the limit of the steady states as the fixed point.
--
--   **Formalization Note** The fixed point is the corrected value `PowerTwoChoices.Limit.fixedPoint` (exponent $(d^i-1)/(d-1)$); the printed (3.4) has $(d^i-d)/(d-1)$, which gives $q^*_1(\infty)=1$ and is not a fixed point of (3.3). $i_0$ is defined from the corrected fixed point, as in App. C. Solutions are `PowerTwoChoices.Limit.IsTrajectory` with values in $\mathcal Y$; $\Psi_\omega$ is `PowerTwoChoices.Limit.potential`, in $[0,\infty]$, and exponential convergence is `ConvergesExponentially`.
-- source:
--   Rutten & Mukherjee, Load Balancing Under Strict Compatibility Constraints, arXiv:2008.07562v2, p. 22, Theorem 4.11, (4.27); pp. 39–40, App. C; p. 12, (3.3)–(3.4)

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_Policy

open Filter Topology
open scoped ENNReal

namespace StrictCompatLB.MeanField

/-- Theorem 4.11 (p. 22; proof App. C, pp. 39–40). Let `0 < λ < 1`, `d ≥ 2` and
`i₀ = min{i ≥ 1 : λ(2 q*_i(∞) + 1) < (1+λ)/2}`. There are positive weights `ω` and `r ∈ (1, 2/(1+λ))`
with `ω_{i₀+i} = ω_{i₀} r^i` for `i ≥ 1` (4.27) such that for every `𝒴`-valued solution `q*` of
(3.3), if `Ψ_ω(0) = ∑_{i ≥ 1} ω_i |q*_i(0) − q*_i(∞)| < ∞` then `Ψ_ω(t)` converges exponentially
to zero. -/
theorem theorem_4_11 (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1) (d : ℕ) (hd : 2 ≤ d) :
    ∃ ω : ℕ → ℝ, (∀ i, 1 ≤ i → 0 < ω i) ∧ ∃ r : ℝ, 1 < r ∧ r < 2 / (1 + lam) ∧
      (∀ i : ℕ, 1 ≤ i → ω (i0Index lam d + i) = ω (i0Index lam d) * r ^ i) ∧
      ∀ s : ℝ → ℕ → ℝ, PowerTwoChoices.Limit.IsTrajectory lam d s →
        (∀ t : ℝ, 0 ≤ t → InY (s t)) →
        PowerTwoChoices.Limit.potential lam d ω (s 0) < ⊤ →
        PowerTwoChoices.Limit.ConvergesExponentially
          (fun t => PowerTwoChoices.Limit.potential lam d ω (s t)) := by sorry

end StrictCompatLB.MeanField
