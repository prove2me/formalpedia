-- Prove2me | Theorems.Thm_RWPI_Limit_eq_31_32
-- name    : RWPI.Limit.eq_31_32
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T18:10:06.812587+00:00
-- url     : https://prove2.me/theorems/fe2ccd6d-597a-4049-914e-e6104909684e
-- title:
--   (31)–(32) — rescaled dual representation $n^{\rho/2}R_n(\theta_*) = \sup_\zeta\{-\zeta^T H_n - M_n(\zeta)\}$
-- statement:
--   Let $W_1, \dots, W_n \in \mathbb R^m$ ($n \ge 1$) be distinct sample points, let $\rho \ge 1$ and $q \in (1, \infty]$, and let $R_n$ be the RWP function with cost $c(u, w) = \|w - u\|_q^\rho$. Let $h : \mathbb R^m \times \mathbb R^l \to \mathbb R^r$ and $\theta_* \in \mathbb R^l$ be such that $h(\cdot, \theta_*)$ is continuously differentiable and $\mathbf 0$ lies in the interior of the convex hull of $\{h(u, \theta_*) : u \in \mathbb R^m\}$. With $H_n = n^{-1/2}\sum_{i=1}^n h(W_i, \theta_*)$ and
--
--   $$
--   M_n(\zeta) = \frac1n \sum_{i=1}^n \sup_{\Delta} \Big\{ \zeta^T \int_0^1 Dh\big(W_i + n^{-1/2}\Delta u\big) \Delta\, du - \|\Delta\|_q^\rho \Big\},
--   $$
--
--   where $Dh = D_w h(\cdot, \theta_*)$, we have
--
--   $$
--   n^{\rho/2} R_n(\theta_*) = \sup_{\zeta \in \mathbb R^r} \big\{ -\zeta^T H_n - M_n(\zeta) \big\} .
--   $$
--
--   The representation isolates the two sources of randomness of the RWP function, the normalized sum $H_n$ and the penalty $M_n$, and is the starting point of the proof of Theorem 3.
--
--   **Formalization Note.** Both sides are compared in the extended reals ($M_n(\zeta)$ may be $+\infty$, making the term $-\infty$); $n^{\rho/2} R_n(\theta_*)$ is computed in $[0, \infty]$. The integral is kept as printed.
-- source:
--   Blanchet, Kang & Murthy, Robust Wasserstein Profile Inference and Applications to Machine Learning, arXiv:1610.05627v4, p. 32, App. A.3, Eqs. (31)–(32)

import Mathlib
import Definitions.Def_RWPI_Limit_rwp
import Definitions.Def_RWPI_Limit_dualRep
import Definitions.Def_WassersteinDRO_Regularization_empiricalDistribution

open MeasureTheory

namespace RWPI.Limit

/-- (31)–(32) (Blanchet, Kang & Murthy, arXiv:1610.05627v4, App. A.3, p. 32): the rescaled dual
representation `n^{ρ/2} R_n(θ*) = sup_ζ { −ζ^T H_n − M_n(ζ) }` of the RWP function with the cost
`c(u, w) = ‖w − u‖_q^ρ`, for distinct sample points, `h(·, θ*)` continuously differentiable and
`0 ∈ int conv {h(u, θ*) : u ∈ ℝ^m}`. Identity in `EReal`. -/
theorem eq_31_32 {m l r n : ℕ} (hn : 0 < n) (w : Fin n → (Fin m → ℝ))
    (hw : Function.Injective w)
    (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ)) (θs : Fin l → ℝ)
    (ρ : ℝ) (hρ : 1 ≤ ρ) (q : ENNReal) (hq : 1 < q)
    (hC1 : ContDiff ℝ 1 fun x => h x θs)
    (hint : (0 : Fin r → ℝ) ∈ interior (convexHull ℝ (Set.range fun u => h u θs))) :
    ((ENNReal.ofReal ((n : ℝ) ^ (ρ / 2)) *
        rwp (costQ q ρ) h θs (WassersteinDRO.Regularization.empiricalDistribution w) : ENNReal)
        : EReal) =
      ⨆ ζ : Fin r → ℝ, (((-(ζ ⬝ᵥ Hn h θs w)) : ℝ) : EReal) - Mn q ρ h θs w ζ := by sorry

end RWPI.Limit
