-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_globalPlace_valuation
-- name    : QEC.Coding.AlgebraicGeometry.AffinePlace.globalPlace_valuation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:42:51.110105+00:00
-- url     : https://prove2.me/theorems/1c308bbd-1803-479b-91d5-7efb07023ddf
-- title:
--   Affine Place: global Place valuation
-- statement:
--   The packaged global valuation is definitionally the original affine adic
--   valuation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/AffineGlobalPlace.lean#L59-L61
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/AffineGlobalPlace.lean#L59-L61

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffineGlobalPlace
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
attribute [local instance] QEC.Coding.AlgebraicGeometry.AffinePlace._p2m_local_instance_439b1c180e_47

theorem QEC.Coding.AlgebraicGeometry.AffinePlace.globalPlace_valuation (P : carrier k F) :
    (globalPlace k F P).valuation = valuation k F P := by sorry
