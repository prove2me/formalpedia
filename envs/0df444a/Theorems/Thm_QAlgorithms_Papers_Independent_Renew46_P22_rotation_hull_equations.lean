-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P22_rotation_hull_equations
-- name    : QAlgorithms.Papers.Independent.Renew46.P22.rotation_hull_equations
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:34:11.633985+00:00
-- url     : https://prove2.me/theorems/ddc483c8-446c-476f-9637-b8925c8654e2
-- title:
--   Defining equations for the hull of a rotation generator
-- statement:
--   Let $F$ be a field of characteristic zero and let $K$ be its specified algebraic closure, with its embedding of $F$. All groups below are geometric subgroups of $\mathrm{GL}_n(K)$, and all closures are relative Zariski closures in that group.
--
--   For the fixed matrix $X=\begin{pmatrix}0&1\\-1&0\end{pmatrix}\in\mathfrak{gl}_2(F)$, let $G(X)$ be the smallest algebraic subgroup whose Lie algebra contains $X$. Its defining equations over $F$ are
--
--   $$G(X)=\{a\in\mathrm{GL}_2(K):a_{11}^2+a_{12}^2-1=0,\ a_{21}+a_{12}=0,\ a_{11}-a_{22}=0\}.$$
--
--   This example fixes the signs and matrix-coordinate order in the semisimple hull construction.
-- source:
--   Constructing algebraic groups from their Lie algebras, arXiv:math/0612557v1, PDF p. 7, Example 8

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P22

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P22

open scoped BigOperators Pointwise

attribute [local instance 100] LieRing.ofAssociativeRing

section Geometric

variable {F K : Type*} [Field F] [hchar : CharZero F] [Field K] [Algebra F K] [hclosure : IsAlgClosure F K]

variable {n : ℕ}

section

include hchar hclosure

/-- Example 8, PDF p.7: these equations define the geometric hull of [[0,1],[-1,0]]. -/
theorem rotation_hull_equations :
    (groupHull F K (Submodule.span F {(!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F)}) : Set (GeometricGL 2 K)) =
      zeros (rotationEquations (F := F)) := by sorry

end

end Geometric

end QAlgorithms.Papers.Independent.Renew46.P22

end
