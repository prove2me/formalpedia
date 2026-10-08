-- Prove2me | Theorems.Thm_SDPT3_ScaleInv_eq_23
-- name    : SDPT3.ScaleInv.eq_23
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T03:13:06.120101+00:00
-- url     : https://prove2.me/theorems/d4ce0e2e-c90b-4eca-962e-7aa80de04943
-- title:
--   (23), p. 9 — HKM: ℰ⁻¹ℱ = G⁻¹Arw(Gx)G⁻¹ = (⟨x,z⟩J + x z̃ᵀ + z̃ xᵀ)/γ²(z), z̃ = (z⁰; −z¹)
-- statement:
--   Let $z \in \mathbb R^q$ be in the interior of the second-order cone, let $x \in \mathbb R^q$, and let $G = G^{\mathrm{HKM}}(z)$ be the HKM scaling (19), with $\mathcal E = \operatorname{Arw}(G^{-1}z)G$ and $\mathcal F = \operatorname{Arw}(Gx)G^{-1}$ as in (8). Write $\tilde z = \bar J z = (z^0; -z^1)$ and $J = \operatorname{diag}(-1, I)$. Then
--   $$\mathcal E^{-1}\mathcal F = G^{-1}\operatorname{Arw}(Gx)\,G^{-1} = \frac{1}{\gamma^2(z)}\Big(\langle x, z\rangle J + x\,\tilde z^\top + \tilde z\, x^\top\Big).$$
--
--   The identity shows that the HKM block of the Schur complement matrix is a diagonal matrix plus a symmetric rank-two matrix.
--
--   **Formalization Note** The page states (23) at an interior iterate; the identity only uses that $z$ is interior, so $x$ is arbitrary here. $\gamma^2(z)$ is written as `gammaSq z` $= (z^0)^2 - \langle z^1, z^1\rangle$, which equals $\gamma(z)^2$ for $z$ in the cone.
-- source:
--   Tütüncü, Toh & Todd, Solving semidefinite-quadratic-linear programs using SDPT3, Math. Program. 95 (2003) 189–217; authors' copy, p. 9, (23)

import Mathlib
import Definitions.Def_SDPT3_ScaleInv_Setting

namespace SDPT3.ScaleInv

open Matrix

theorem eq_23 {k : ℕ} (x z : Fin (k + 1) → ℝ) (hz : socInt z) :
    (calE (GHKM z) z)⁻¹ * calF (GHKM z) x = (GHKM z)⁻¹ * arw (GHKM z *ᵥ x) * (GHKM z)⁻¹ ∧
      (GHKM z)⁻¹ * arw (GHKM z *ᵥ x) * (GHKM z)⁻¹ =
        (gammaSq z)⁻¹ • ((x ⬝ᵥ z) • J k + vecMulVec x (Jbar k *ᵥ z) +
          vecMulVec (Jbar k *ᵥ z) x) := by sorry

end SDPT3.ScaleInv
