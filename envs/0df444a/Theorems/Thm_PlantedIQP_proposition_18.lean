-- Prove2me | Theorems.Thm_PlantedIQP_proposition_18
-- name    : PlantedIQP.proposition_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:21:14.140768+00:00
-- url     : https://prove2.me/theorems/46d8e505-97b8-4a4d-b63b-f9c2a4435ad2
-- title:
--   Proposition 18 — $T_f$, Hessian slices and $Q_f$ under $GL(n,\mathbb F_2)$
-- statement:
--   Let $f$ be a cubic polynomial, $A\in GL(n,\mathbb F_2)$ and $g=f\circ A$. Then
--
--   1. $(f\circ A)^{(3)}=(f^{(3)}\circ A)^{(3)}$, i.e. the cubic part of $g$ depends only on the cubic part of $f$;
--   2. $T_g(u,v,w)=T_f(Au,Av,Aw)$ for all $u,v,w$;
--   3. as matrices of bilinear forms, $T^g_u=A^{\mathsf T}T^f_{Au}A$, and consequently
--
--   $$
--   H^g_u+Q_g=A^{\mathsf T}\big(H^f_{Au}+Q_f\big)A .
--   $$
--
--   These rules transport independent spaces along $GL(n,\mathbb F_2)$, which is how a planted coordinate space is hidden.
--
--   Differences from the source:
--   - encoding: (f ◦ A)^{(3)} = (f^{(3)} ◦ A)^{(3)} = g^{(3)} → (f.comp A).cubicPart = (f.cubicPart.comp A).cubicPart; reason: the second equality is the definition g = f ◦ A
-- source:
--   Bläser, Gullans, Hangleiter, Liu, Qiao, Verifiable quantum advantage based on polynomials with planted structures, arXiv:2609.39918 (sha256 6e261694…), Proposition 18, p.15

import Mathlib
import Definitions.Def_PlantedIQP_comp
import Definitions.Def_PlantedIQP_triForm
import Definitions.Def_PlantedIQP_hessSlice

set_option autoImplicit false

namespace PlantedIQP

/-- Bläser, Gullans, Hangleiter, Liu, Qiao, *Verifiable quantum advantage based on polynomials with
planted structures*, arXiv:2609.39918 (sha256 6e261694…), Proposition 18, p.15: for a cubic polynomial `f`, `A ∈ GL(n, 𝔽₂)` and
`g = f ◦ A`: (1) `(f ◦ A)^{(3)} = (f^{(3)} ◦ A)^{(3)} = g^{(3)}`; (2) `T_g(u, v, w) = T_f(Au, Av, Aw)`
for all `u, v, w`; (3) as matrices of bilinear forms `T^g_u = Aᵀ T^f_{Au} A`, and consequently
`H^g_u + Q_g = Aᵀ (H^f_{Au} + Q_f) A`. -/
theorem proposition_18 {n : ℕ} (f : CubicPoly n) (A : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
    (f.comp A).cubicPart = (f.cubicPart.comp A).cubicPart ∧
      (∀ u v w : Vec n, triForm (f.comp A) u v w =
        triForm f (Matrix.mulVec (A : Matrix (Fin n) (Fin n) (ZMod 2)) u)
          (Matrix.mulVec (A : Matrix (Fin n) (Fin n) (ZMod 2)) v)
          (Matrix.mulVec (A : Matrix (Fin n) (Fin n) (ZMod 2)) w)) ∧
      ∀ u : Vec n,
        sliceMatrix (f.comp A) u = Matrix.transpose (A : Matrix (Fin n) (Fin n) (ZMod 2)) *
            sliceMatrix f (Matrix.mulVec (A : Matrix (Fin n) (Fin n) (ZMod 2)) u) *
              (A : Matrix (Fin n) (Fin n) (ZMod 2)) ∧
          hessSlice (f.comp A) u + quadMatrix (f.comp A) =
            Matrix.transpose (A : Matrix (Fin n) (Fin n) (ZMod 2)) *
              (hessSlice f (Matrix.mulVec (A : Matrix (Fin n) (Fin n) (ZMod 2)) u) + quadMatrix f) *
                (A : Matrix (Fin n) (Fin n) (ZMod 2)) := by sorry

end PlantedIQP
