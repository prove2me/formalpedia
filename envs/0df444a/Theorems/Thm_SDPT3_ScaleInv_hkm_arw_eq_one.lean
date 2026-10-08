-- Prove2me | Theorems.Thm_SDPT3_ScaleInv_hkm_arw_eq_one
-- name    : SDPT3.ScaleInv.hkm_arw_eq_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T03:13:31.762988+00:00
-- url     : https://prove2.me/theorems/bad6965f-dfcc-4896-b404-95bb3379f6a4
-- title:
--   §2.3.2, p. 9 — HKM: G is invertible, Ge₁ = z, and Arw(G⁻¹z) = I
-- statement:
--   Let $z \in \mathbb R^{q}$ lie in the interior of the second-order cone ($z^0 > 0$ and $\gamma^2(z) > 0$), and let $G = G^{\mathrm{HKM}}(z)$ be the HKM scaling matrix (19). Then $G$ is invertible, $G e_1 = z$, and
--   $$\operatorname{Arw}(G^{-1} z) = I.$$
--
--   This is the remark following (23); it says that for the HKM scaling $\mathcal E = \operatorname{Arw}(G^{-1}z)G = G$.
--
--   **Formalization Note** Invertibility and $Ge_1 = z$ are stated together with the remark because $G^{-1}$ is Lean's `Matrix.inv`, which is $0$ on singular input.
-- source:
--   Tütüncü, Toh & Todd, Solving semidefinite-quadratic-linear programs using SDPT3, Math. Program. 95 (2003) 189–217; authors' copy, p. 9, §2.3.2, remark after (23)

import Mathlib
import Definitions.Def_SDPT3_ScaleInv_Setting

namespace SDPT3.ScaleInv

open Matrix

theorem hkm_arw_eq_one {k : ℕ} (z : Fin (k + 1) → ℝ) (hz : socInt z) :
    IsUnit (GHKM z).det ∧ GHKM z *ᵥ e1 k = z ∧ arw ((GHKM z)⁻¹ *ᵥ z) = 1 := by sorry

end SDPT3.ScaleInv
