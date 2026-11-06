-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_globalPlace_surjective
-- name    : QEC.Coding.AlgebraicGeometry.AffinePlace.globalPlace_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:45:02.939242+00:00
-- url     : https://prove2.me/theorems/2fed0eea-d1c8-4c50-b62a-21c56d935cd6
-- title:
--   Affine Place: global Place surjective
-- statement:
--   The affine global place carries the surjectivity proof supplied by the
--   height-one-prime adic-valuation API.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/AffineGlobalPlace.lean#L65-L67
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/AffineGlobalPlace.lean#L65-L67

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

theorem QEC.Coding.AlgebraicGeometry.AffinePlace.globalPlace_surjective (P : carrier k F) :
    Function.Surjective (globalPlace k F P).valuation := by sorry
