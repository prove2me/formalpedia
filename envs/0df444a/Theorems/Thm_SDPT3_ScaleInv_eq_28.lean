-- Prove2me | Theorems.Thm_SDPT3_ScaleInv_eq_28
-- name    : SDPT3.ScaleInv.eq_28
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T03:13:22.366485+00:00
-- url     : https://prove2.me/theorems/981497e8-c6eb-4a62-a098-787b6eeef2fc
-- title:
--   (28), p. 11 — HKM and NT: ℰ⁻¹(σµe₁ − T_G(x,z)) = (σµ/γ²(z))(z⁰; −z¹) − x
-- statement:
--   Let $x, z \in \mathbb R^q$ lie in the interior of the second-order cone, let $G$ be either the HKM scaling (19) or the NT scaling (21) at $(x, z)$, and let $\mathcal E = \operatorname{Arw}(G^{-1}z)G$, $T_G(x,z) = \operatorname{Arw}(Gx)(G^{-1}z)$. For all real $\sigma, \mu$,
--   $$\mathcal E^{-1}\big(\sigma\mu\, e_1 - T_G(x, z)\big) = \frac{\sigma\mu}{\gamma^2(z)}\begin{bmatrix} z^0 \\ -z^1 \end{bmatrix} - x.$$
--
--   The left side is $\mathcal E_i^{-1}(R_c)_i$, the term needed in the right-hand side $h$ of the Schur complement equation (12). The paper states the formula for HKM and then notes that it also holds for NT.
--
--   **Formalization Note** $\sigma\mu$ enters only as a product, so $\sigma$ and $\mu$ are arbitrary reals here; in (4), $\mu = \langle x, z\rangle / n_q$ is shared by all blocks.
-- source:
--   Tütüncü, Toh & Todd, Solving semidefinite-quadratic-linear programs using SDPT3, Math. Program. 95 (2003) 189–217; authors' copy, p. 11, (28), and the sentence before (30)

import Mathlib
import Definitions.Def_SDPT3_ScaleInv_Setting

namespace SDPT3.ScaleInv

open Matrix

theorem eq_28 {k : ℕ} (dir : Dir) (x z : Fin (k + 1) → ℝ) (hx : socInt x) (hz : socInt z)
    (σ μ : ℝ) :
    (calE (Gdir dir x z) z)⁻¹ *ᵥ ((σ * μ) • e1 k - TG (Gdir dir x z) x z) =
      (σ * μ / gammaSq z) • (Jbar k *ᵥ z) - x := by sorry

end SDPT3.ScaleInv
