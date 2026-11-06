-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_residueAlgebra_algebraMap
-- name    : QEC.Coding.AlgebraicGeometry.AffinePlace.residueAlgebra_algebraMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:13:25.087482+00:00
-- url     : https://prove2.me/theorems/fa50d900-c9bd-4409-b6eb-4d825514b44d
-- title:
--   Affine Place: residue Algebra algebra Map
-- statement:
--   The scalar map of the explicitly selected affine residue algebra is the
--   actual constant-reduction map.  This is the public boundary for clients that
--   need the algebra map itself, rather than the implementation of `toAlgebra`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/AffineResidue.lean#L47-L50
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/AffineResidue.lean#L47-L50

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffineResidue
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero
open QEC.Coding.AlgebraicGeometry.AffinePlace
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]

theorem QEC.Coding.AlgebraicGeometry.AffinePlace.residueAlgebra_algebraMap (P : carrier k F) :
    letI : Algebra k (residueField k F P) := residueAlgebra k F P
    algebraMap k (residueField k F P) = constantsToResidue k F P := by sorry
