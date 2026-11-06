-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_RationalPlace_constantsToResidue_bijective
-- name    : QEC.Coding.AlgebraicGeometry.RationalPlace.constantsToResidue_bijective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:45:37.006698+00:00
-- url     : https://prove2.me/theorems/2ec16c41-3347-4371-965d-56f0ea22da09
-- title:
--   Rational Place: constants To Residue bijective
-- statement:
--   The canonical constant-reduction map is bijective at a rational place.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/RationalPlace.lean#L134-L144
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/RationalPlace.lean#L134-L144

import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.RationalPlace
variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]

theorem QEC.Coding.AlgebraicGeometry.RationalPlace.constantsToResidue_bijective (Q : RationalPlace k F) :
    Function.Bijective (GlobalPlace.constantsToResidue Q.place) := by sorry
