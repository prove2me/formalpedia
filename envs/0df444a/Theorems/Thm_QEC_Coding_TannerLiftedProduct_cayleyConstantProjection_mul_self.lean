-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_cayleyConstantProjection_mul_self
-- name    : QEC.Coding.TannerLiftedProduct.cayleyConstantProjection_mul_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:11:50.757882+00:00
-- url     : https://prove2.me/theorems/6d1a4e52-9ac3-4464-854a-fc716d1a35ac
-- title:
--   Tanner Lifted Product: cayley Constant Projection mul self
-- statement:
--   The averaging operator onto constants is idempotent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CayleySpectrum.lean#L97-L104
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CayleySpectrum.lean#L97-L104

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSpectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Mathlib.LinearAlgebra.Trace
import Mathlib.RepresentationTheory.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_CayleySpectrum
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe v
variable {G W : Type v}
  [Group G] [Fintype G] [Fintype W]
  [DecidableEq G]

theorem QEC.Coding.TannerLiftedProduct.cayleyConstantProjection_mul_self :
    cayleyConstantProjection (G := G) * cayleyConstantProjection =
      cayleyConstantProjection := by sorry
