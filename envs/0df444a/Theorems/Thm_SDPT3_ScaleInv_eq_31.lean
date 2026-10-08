-- Prove2me | Theorems.Thm_SDPT3_ScaleInv_eq_31
-- name    : SDPT3.ScaleInv.eq_31
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T03:13:15.557349+00:00
-- url     : https://prove2.me/theorems/1b0fd644-6a9d-4c53-a223-d20e4b8cb715
-- title:
--   (31), p. 12 — if FᵀJ̄F = J̄ then F is invertible and FᵀJ̄ = J̄F⁻¹, J̄F = F⁻ᵀJ̄, J̄Fᵀ = F⁻¹J̄
-- statement:
--   Let $\bar J = \operatorname{diag}(1, -I)$ on $\mathbb R^{q}$ and let $F$ be a real $q \times q$ matrix with $F^\top \bar J F = \bar J$. Then $F$ is invertible and
--   $$F^\top \bar J = \bar J F^{-1},\qquad \bar J F = F^{-\top} \bar J,\qquad \bar J F^\top = F^{-1} \bar J.$$
--
--   These are the identities (31) used throughout the proof of Proposition 1 to move a scaling matrix across $\bar J$.
--
--   **Formalization Note** The paper asserts (31) for every $F_i$ in the automorphism group $\mathcal G_i$; it holds exactly for those with $F^\top \bar J F = \bar J$ (the case $\lambda = 1$). For $\lambda F$ with $\lambda \ne 1$ the first identity reads $F^\top \bar J F = \lambda^2 \bar J$. The statement therefore takes the first identity of (31) as its hypothesis, and does not need $F_{00} > 0$. Invertibility is part of the conclusion because Lean's `F⁻¹` is $0$ for singular $F$.
-- source:
--   Tütüncü, Toh & Todd, Solving semidefinite-quadratic-linear programs using SDPT3, Math. Program. 95 (2003) 189–217; authors' copy, p. 12, proof of Proposition 1, (31)

import Mathlib
import Definitions.Def_SDPT3_ScaleInv_Setting

namespace SDPT3.ScaleInv

open Matrix

theorem eq_31 {k : ℕ} (F : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
    (hF : Fᵀ * Jbar k * F = Jbar k) :
    IsUnit F.det ∧ Fᵀ * Jbar k = Jbar k * F⁻¹ ∧ Jbar k * F = (F⁻¹)ᵀ * Jbar k ∧
      Jbar k * Fᵀ = F⁻¹ * Jbar k := by sorry

end SDPT3.ScaleInv
