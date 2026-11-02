-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P79_corollary_3_3_1
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P79.corollary_3_3_1
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:21:32.037276+00:00
-- url     : https://prove2.me/theorems/c08cc495-244d-4777-94af-a58001f732ee
-- title:
--   Quasi-projectivity of irreducible algebraic monoids
-- statement:
--   Let $k$ be an algebraically closed field of characteristic zero. Let $M$ be a separated reduced $k$-scheme of finite type which is irreducible and carries an associative regular multiplication with an identity. Then
--
--   $$\exists n\in\mathbb N,\quad\exists i:M\longrightarrow\mathbb P_k^n,\qquad i\text{ is a locally closed immersion over }k.$$
--
--   Thus every irreducible algebraic monoid is quasi-projective, including non-affine and non-normal monoids. Quasi-projectivity is a conclusion, not part of the standing definition of variety.
-- source:
--   Local structure of algebraic monoids, arXiv:0709.1255v2, PDF p. 20, Corollary 3.3.1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P79

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

open CategoryTheory.MonObj

open scoped CategoryTheory.MonObj Pointwise

universe u

namespace QAlgorithms.Papers.Independent.Intakethird100.P79

variable (k : Type u) [Field k]

variable {k}

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Corollary 3.3.1, PDF p. 20: every irreducible algebraic monoid is
quasi-projective. No affine, normal, or reductive assumption is imposed. -/
theorem corollary_3_3_1 [IsAlgClosed k] [CharZero k]
    (M : KScheme k) [MonObj M] [IsVariety k M] [IrreducibleSpace M.left] :
    IsQuasiProjective M := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P79

end
