-- Prove2me | Theorems.Thm_WassDDRO_Reduction_program12f_eq_program11
-- name    : WassDDRO.Reduction.program12f_eq_program11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:49:04.113236+00:00
-- url     : https://prove2.me/theorems/a06a1f04-6809-4a89-b57e-36de727847f3
-- title:
--   Proof of Theorem 4.2, p. 13 — under Assumption 4.1, the optimal values of (12f) and (11) coincide
-- statement:
--   Let $E$, $\Xi$, $\ell_1,\dots,\ell_K$ and samples $\hat\xi_1,\dots,\hat\xi_N\in\Xi$ be as in Theorem 4.2 ($K,N\ge1$), and suppose Assumption 4.1 holds. Then for every $\varepsilon\ge0$ the optimal value of (12f),
--   $$\inf_{\lambda,s_i,z_{ik}}\Big\{\lambda\varepsilon+\frac1N\sum_i s_i:\ [-\ell_k+\chi_\Xi]^*(z_{ik})-\langle z_{ik},\hat\xi_i\rangle\le s_i,\ \|z_{ik}\|_*\le\lambda\ \ \forall i,k\Big\},$$
--   equals the optimal value of (11),
--   $$\inf_{\lambda,s_i,z_{ik},\nu_{ik}}\Big\{\lambda\varepsilon+\frac1N\sum_i s_i:\ [-\ell_k]^*(z_{ik}-\nu_{ik})+\sigma_\Xi(\nu_{ik})-\langle z_{ik},\hat\xi_i\rangle\le s_i,\ \|z_{ik}\|_*\le\lambda\ \ \forall i,k\Big\}.$$
--
--   The constraint of (11) replaces the conjugate of the sum $-\ell_k+\chi_\Xi$ by the inf-convolution of the conjugates of $-\ell_k$ and $\chi_\Xi$ (the support function $\sigma_\Xi$). The two constraint functions differ by a lower-semicontinuous closure, so the statement is an equality of optimal values, not of feasible sets.
--
--   **Formalization Note** The sum $[-\ell_k]^*(z-\nu)+\sigma_\Xi(\nu)$ is taken in `EReal`. Under Assumption 4.1 neither summand is $-\infty$ ($-\ell_k$ is finite somewhere and $\Xi$ contains the samples), so Mathlib's $\top+\bot=\bot$ never arises.
-- source:
--   Mohajerin Esfahani & Kuhn, arXiv:1505.05116v3, proof of Theorem 4.2, p. 13 ("(12f) is indeed equivalent to (11) under Assumption 4.1"); program (11), p. 12

import Mathlib
import Definitions.Def_WassDDRO_Reduction_Setting

open MeasureTheory Filter Topology

namespace WassDDRO.Reduction

/-- Proof of Theorem 4.2, p. 13: under Assumption 4.1, for any `ε ≥ 0` the optimal values of
(12f) and (11) coincide. -/
theorem program12f_eq_program11 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {K N : ℕ} (hK : 0 < K) (hN : 0 < N) (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (hmeas : ∀ k, Measurable (ℓ k)) (ξhat : Fin N → E) (hξ : ∀ i, ξhat i ∈ Ξ)
    (ε : ℝ) (hε : 0 ≤ ε) (hA : Assumption41 Ξ ℓ) :
    program12fValue ε Ξ ξhat ℓ = program11Value ε Ξ ξhat ℓ := by sorry

end WassDDRO.Reduction
