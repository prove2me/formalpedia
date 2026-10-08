-- Prove2me | Theorems.Thm_RWPI_Limit_eq_42
-- name    : RWPI.Limit.eq_42
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T17:50:44.263135+00:00
-- url     : https://prove2.me/theorems/e2ea7bb5-30fb-4329-a19b-364c6aaacdfe
-- title:
--   (42) — $\max_\Delta\{v^T\Delta - \|\Delta\|_q^\rho\} = \|v\|_p^{\rho/(\rho-1)}(1/\rho)^{1/(\rho-1)}(1-1/\rho)$
-- statement:
--   Let $\rho > 1$, let $p, q \in [1, \infty]$ be conjugate exponents, $1/p + 1/q = 1$, and let $v \in \mathbb R^m$ (in the paper, $v$ is the row vector $\zeta^T Dh(W_i)$). Then the supremum of $\Delta \mapsto v^T \Delta - \|\Delta\|_q^\rho$ over $\Delta \in \mathbb R^m$ is attained, and
--
--   $$
--   \max_{\Delta \in \mathbb R^m} \big\{ v^T \Delta - \|\Delta\|_q^\rho \big\} = \|v\|_p^{\rho/(\rho - 1)} \Big(\frac1\rho\Big)^{1/(\rho - 1)} \Big(1 - \frac1\rho\Big) .
--   $$
--
--   This closed form identifies the limit of the penalty $M_n(\zeta)$ in the proof of Theorem 3 and produces the constant $\kappa(\rho) = (1/\rho)^{1/(\rho-1)}(1 - 1/\rho)$ of (45).
--
--   **Formalization Note.** The norms are Mathlib's `PiLp` norms, so $q = \infty$ or $p = \infty$ is allowed. The statement holds for all conjugate pairs including $q = 1$; the paper's surrounding text assumes $q > 1$, which is not needed for this identity.
-- source:
--   Blanchet, Kang & Murthy, Robust Wasserstein Profile Inference and Applications to Machine Learning, arXiv:1610.05627v4, p. 36, App. A.3, proof of Theorem 3, Eq. (42)

import Mathlib

namespace RWPI.Limit

/-- (42) (Blanchet, Kang & Murthy, arXiv:1610.05627v4, App. A.3, proof of Theorem 3, p. 36): for
`ρ > 1`, Hölder-conjugate exponents `p, q ∈ [1, ∞]` and any `v ∈ ℝ^m` (standing for the row vector
`ζ^T Dh(W_i)`), the supremum `sup_Δ { v^T Δ − ‖Δ‖_q^ρ }` over `Δ ∈ ℝ^m` is attained and equals
`‖v‖_p^{ρ/(ρ−1)} (1/ρ)^{1/(ρ−1)} (1 − 1/ρ)`. -/
theorem eq_42 {m : ℕ} (ρ : ℝ) (hρ : 1 < ρ) (q p : ENNReal) (hpq : p.HolderConjugate q)
    (v : Fin m → ℝ) :
    IsGreatest (Set.range fun Δ : Fin m → ℝ => v ⬝ᵥ Δ - ‖WithLp.toLp q Δ‖ ^ ρ)
      (‖WithLp.toLp p v‖ ^ (ρ / (ρ - 1)) * (1 / ρ) ^ (1 / (ρ - 1)) * (1 - 1 / ρ)) := by sorry

end RWPI.Limit
