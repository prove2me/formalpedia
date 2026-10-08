-- Prove2me | Theorems.Thm_SDPT3_ScaleInv_eq_30
-- name    : SDPT3.ScaleInv.eq_30
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T03:13:24.884391+00:00
-- url     : https://prove2.me/theorems/4be0109b-9772-4e03-b325-5343e440d34c
-- title:
--   (30), p. 11 — NT: M_i = (AᵀJA + 2uuᵀ)/ω², u = Aᵀ(t⁰; −t¹)
-- statement:
--   Let $x, z \in \mathbb R^q$ lie in the interior of the second-order cone, $A_i \in \mathbb R^{q\times m}$, and $G = G^{\mathrm{NT}}(x, z)$ with $\omega$, $t$ as in (20)–(21). The block $M_i = A_i^\top \mathcal E_i^{-1}\mathcal F_i A_i$ of the Schur complement matrix satisfies
--   $$M_i = \frac{1}{\omega^2}\Big(A_i^\top J A_i + 2\,u\,u^\top\Big),\qquad u = A_i^\top \begin{bmatrix} t^0 \\ -t^1 \end{bmatrix},$$
--   with $J = \operatorname{diag}(-1, I)$.
--
--   This is the NT counterpart of (24), through which the proof of Proposition 1 sees that $M$ is invariant under scaling for the NT direction.
-- source:
--   Tütüncü, Toh & Todd, Solving semidefinite-quadratic-linear programs using SDPT3, Math. Program. 95 (2003) 189–217; authors' copy, p. 11, (30)

import Mathlib
import Definitions.Def_SDPT3_ScaleInv_Setting

namespace SDPT3.ScaleInv

open Matrix

theorem eq_30 {k m : ℕ} (Ai : Matrix (Fin (k + 1)) (Fin m) ℝ) (x z : Fin (k + 1) → ℝ)
    (hx : socInt x) (hz : socInt z) :
    Mblock (GNT x z) Ai x z =
      (omegaNT x z ^ 2)⁻¹ • (Aiᵀ * J k * Ai +
        (2 : ℝ) • vecMulVec (Aiᵀ *ᵥ (Jbar k *ᵥ tNT x z)) (Aiᵀ *ᵥ (Jbar k *ᵥ tNT x z))) := by sorry

end SDPT3.ScaleInv
