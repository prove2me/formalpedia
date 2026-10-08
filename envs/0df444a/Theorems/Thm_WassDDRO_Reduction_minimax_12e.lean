-- Prove2me | Theorems.Thm_WassDDRO_Reduction_minimax_12e
-- name    : WassDDRO.Reduction.minimax_12e
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:48:34.550068+00:00
-- url     : https://prove2.me/theorems/5de1729e-c4b5-4865-a9f0-65725f61cba5
-- title:
--   Proof of Theorem 4.2, (12d)–(12e), p. 13 — under Assumption 4.1, the minimax interchange in each constraint is exact
-- statement:
--   Let $E$ be a finite-dimensional real normed space with dual norm $\|\cdot\|_*$, and let $\Xi$, $\ell_1,\dots,\ell_K$ and samples $\hat\xi_1,\dots,\hat\xi_N\in\Xi$ be as in Theorem 4.2, with Assumption 4.1 in force. Fix $\lambda\ge0$, a sample index $i$ and a piece $k$. Then
--   $$\sup_{\xi\in\Xi}\big(\ell_k(\xi)-\lambda\|\xi-\hat\xi_i\|\big)=\min_{\|z\|_*\le\lambda}\ \sup_{\xi\in\Xi}\big(\ell_k(\xi)-\langle z,\xi-\hat\xi_i\rangle\big),$$
--   and the minimum on the right is attained by some $z$ with $\|z\|_*\le\lambda$.
--
--   Since $\lambda\|\xi-\hat\xi_i\|=\max_{\|z\|_*\le\lambda}\langle z,\xi-\hat\xi_i\rangle$, the left side is the constraint function of (12d) and the right side that of (12e); the statement says that the inequality between (12d) and (12e) is an equality, by the minimax theorem over the compact dual ball.
--
--   **Formalization Note** Both sides are extended reals; the infimum over the dual ball is written as an infimum over the set $\{z:\|z\|_*\le\lambda\}$ and its attainment is stated separately. The left side is written with $\lambda\|\xi-\hat\xi_i\|$ rather than with the inner maximum over $z$.
-- source:
--   Mohajerin Esfahani & Kuhn, arXiv:1505.05116v3, proof of Theorem 4.2, (12d) p. 12 and (12e) p. 13; minimax step p. 13

import Mathlib
import Definitions.Def_WassDDRO_Reduction_Setting

open MeasureTheory Filter Topology

namespace WassDDRO.Reduction

/-- Proof of Theorem 4.2, (12d)–(12e), p. 13: under Assumption 4.1, for each `λ ≥ 0`, `i`, `k`,
the constraint function of (12d) equals that of (12e) (minimax), and the minimum over the dual
ball `‖z‖_* ≤ λ` is attained. -/
theorem minimax_12e {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {K N : ℕ} (hK : 0 < K) (hN : 0 < N) (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (hmeas : ∀ k, Measurable (ℓ k)) (ξhat : Fin N → E) (hξ : ∀ i, ξhat i ∈ Ξ)
    (hA : Assumption41 Ξ ℓ) (lam : ℝ) (hlam : 0 ≤ lam) (i : Fin N) (k : Fin K) :
    (⨆ ξ ∈ Ξ, ℓ k ξ - ((lam * ‖ξ - ξhat i‖ : ℝ) : EReal))
        = (⨅ z ∈ {z : StrongDual ℝ E | ‖z‖ ≤ lam},
            ⨆ ξ ∈ Ξ, ℓ k ξ - ((z (ξ - ξhat i) : ℝ) : EReal)) ∧
      ∃ z : StrongDual ℝ E, ‖z‖ ≤ lam ∧
        (⨆ ξ ∈ Ξ, ℓ k ξ - ((z (ξ - ξhat i) : ℝ) : EReal))
          = (⨆ ξ ∈ Ξ, ℓ k ξ - ((lam * ‖ξ - ξhat i‖ : ℝ) : EReal)) := by sorry

end WassDDRO.Reduction
