-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_cayleyConstantProjection_mul_centeredGeneratorSum_action
-- name    : QEC.Coding.TannerLiftedProduct.cayleyConstantProjection_mul_centeredGeneratorSum_action
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:16:56.841458+00:00
-- url     : https://prove2.me/theorems/a50f6e07-37c4-4fc7-897f-afd85b6ba7a7
-- title:
--   Tanner Lifted Product: cayley Constant Projection mul centered Generator Sum action
-- statement:
--   Centered Cayley adjacency annihilates the constant projection on the
--   left.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CayleySpectrum.lean#L249-L258
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CayleySpectrum.lean#L249-L258

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

theorem QEC.Coding.TannerLiftedProduct.cayleyConstantProjection_mul_centeredGeneratorSum_action
    (label : W → G) :
    cayleyConstantProjection *
          cayleyRightRegularRepresentation.asAlgebraHom
            (cayleyCenteredGeneratorSum label) =
      0 := by sorry
