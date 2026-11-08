-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_cayleyConstantProjection_mul_generatorSum_action
-- name    : QEC.Coding.TannerLiftedProduct.cayleyConstantProjection_mul_generatorSum_action
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:12:35.797727+00:00
-- url     : https://prove2.me/theorems/dc434c37-7f6c-4e0a-ad20-13511485842c
-- title:
--   Tanner Lifted Product: cayley Constant Projection mul generator Sum action
-- statement:
--   Averaging after labelled Cayley adjacency also multiplies by the number
--   of labels.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CayleySpectrum.lean#L122-L144
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CayleySpectrum.lean#L122-L144

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

theorem QEC.Coding.TannerLiftedProduct.cayleyConstantProjection_mul_generatorSum_action
    (label : W → G) :
    cayleyConstantProjection *
          cayleyRightRegularRepresentation.asAlgebraHom
            (cayleyGeneratorSum label) =
      (Fintype.card W : ℂ) • cayleyConstantProjection := by sorry
