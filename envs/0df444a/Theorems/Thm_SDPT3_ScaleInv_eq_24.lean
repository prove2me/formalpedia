-- Prove2me | Theorems.Thm_SDPT3_ScaleInv_eq_24
-- name    : SDPT3.ScaleInv.eq_24
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T03:13:12.999828+00:00
-- url     : https://prove2.me/theorems/a06df294-c121-464a-ac9d-5d2b2123042c
-- title:
--   (24)–(25), p. 9 — HKM: M_i = (⟨x,z⟩/γ²(z)) AᵀJA + u vᵀ + v uᵀ, u = Aᵀx, v = Aᵀ(z⁰; −z¹)/γ²(z)
-- statement:
--   Let $z \in \mathbb R^q$ be in the interior of the second-order cone, $x \in \mathbb R^q$, $A_i \in \mathbb R^{q\times m}$, and $G = G^{\mathrm{HKM}}(z)$. The block $M_i = A_i^\top \mathcal E_i^{-1}\mathcal F_i A_i$ of the Schur complement matrix (22) satisfies
--   $$M_i = \frac{\langle x, z\rangle}{\gamma^2(z)} A_i^\top J A_i + u\,v^\top + v\,u^\top,\qquad u = A_i^\top x,\quad v = A_i^\top\Big(\frac{1}{\gamma^2(z)}\begin{bmatrix} z^0 \\ -z^1\end{bmatrix}\Big),$$
--   with $J = \operatorname{diag}(-1, I)$ as in (25).
--
--   This is the formula SDPT3 uses to assemble the HKM Schur complement matrix, and the one through which the proof of Proposition 1 sees that $M$ is invariant under scaling.
--
--   **Formalization Note** As for (23), only interiority of $z$ is used, and $x$ is arbitrary.
-- source:
--   Tütüncü, Toh & Todd, Solving semidefinite-quadratic-linear programs using SDPT3, Math. Program. 95 (2003) 189–217; authors' copy, p. 8, (22); p. 9, (24)–(25)

import Mathlib
import Definitions.Def_SDPT3_ScaleInv_Setting

namespace SDPT3.ScaleInv

open Matrix

theorem eq_24 {k m : ℕ} (Ai : Matrix (Fin (k + 1)) (Fin m) ℝ) (x z : Fin (k + 1) → ℝ)
    (hz : socInt z) :
    Mblock (GHKM z) Ai x z =
      ((x ⬝ᵥ z) / gammaSq z) • (Aiᵀ * J k * Ai) +
        vecMulVec (Aiᵀ *ᵥ x) (Aiᵀ *ᵥ ((gammaSq z)⁻¹ • (Jbar k *ᵥ z))) +
        vecMulVec (Aiᵀ *ᵥ ((gammaSq z)⁻¹ • (Jbar k *ᵥ z))) (Aiᵀ *ᵥ x) := by sorry

end SDPT3.ScaleInv
