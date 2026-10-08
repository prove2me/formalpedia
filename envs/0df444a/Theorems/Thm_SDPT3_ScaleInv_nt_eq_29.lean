-- Prove2me | Theorems.Thm_SDPT3_ScaleInv_nt_eq_29
-- name    : SDPT3.ScaleInv.nt_eq_29
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T03:13:27.539823+00:00
-- url     : https://prove2.me/theorems/5bca1363-3726-4f5d-b0d0-e9f874bc3d5e
-- title:
--   (29), p. 11 — NT: Gx = G⁻¹z and ℰ⁻¹ℱ = G⁻² = (J + 2 t̃ t̃ᵀ)/ω², t̃ = (t⁰; −t¹)
-- statement:
--   Let $x, z \in \mathbb R^q$ lie in the interior of the second-order cone, and let $G = G^{\mathrm{NT}}(x, z)$ be the NT scaling (21), with $\omega$ and $t$ as in (20)–(21). Then $G$ is invertible,
--   $$G x = G^{-1} z,$$
--   and, with $\mathcal E = \operatorname{Arw}(G^{-1}z)G$, $\mathcal F = \operatorname{Arw}(Gx)G^{-1}$, $\tilde t = (t^0; -t^1)$ and $J = \operatorname{diag}(-1, I)$,
--   $$\mathcal E^{-1}\mathcal F = G^{-2} = \frac{1}{\omega^2}\Big(J + 2\,\tilde t\,\tilde t^\top\Big).$$
--
--   This is the NT analogue of (23): the NT block of the Schur complement matrix is a diagonal matrix plus a rank-one matrix.
--
--   **Formalization Note** Invertibility of $G$ is part of the conclusion because $G^{-1}$ is Lean's `Matrix.inv`, which is $0$ on singular input. $G^{-2}$ is written $G^{-1}G^{-1}$.
-- source:
--   Tütüncü, Toh & Todd, Solving semidefinite-quadratic-linear programs using SDPT3, Math. Program. 95 (2003) 189–217; authors' copy, p. 11, (29) and the sentence before it

import Mathlib
import Definitions.Def_SDPT3_ScaleInv_Setting

namespace SDPT3.ScaleInv

open Matrix

theorem nt_eq_29 {k : ℕ} (x z : Fin (k + 1) → ℝ) (hx : socInt x) (hz : socInt z) :
    IsUnit (GNT x z).det ∧ GNT x z *ᵥ x = (GNT x z)⁻¹ *ᵥ z ∧
      (calE (GNT x z) z)⁻¹ * calF (GNT x z) x = (GNT x z)⁻¹ * (GNT x z)⁻¹ ∧
      (GNT x z)⁻¹ * (GNT x z)⁻¹ =
        (omegaNT x z ^ 2)⁻¹ • (J k + (2 : ℝ) • vecMulVec (Jbar k *ᵥ tNT x z) (Jbar k *ᵥ tNT x z)) := by sorry

end SDPT3.ScaleInv
