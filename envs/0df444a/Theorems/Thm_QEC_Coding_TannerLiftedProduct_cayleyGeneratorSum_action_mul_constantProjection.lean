-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_cayleyGeneratorSum_action_mul_constantProjection
-- name    : QEC.Coding.TannerLiftedProduct.cayleyGeneratorSum_action_mul_constantProjection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:12:39.471203+00:00
-- url     : https://prove2.me/theorems/06b4e3d5-827b-43f1-947d-5dedd297d7ca
-- title:
--   Tanner Lifted Product: cayley Generator Sum action mul constant Projection
-- statement:
--   A labelled Cayley adjacency operator acts on constants by the number of
--   labels.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CayleySpectrum.lean#L108-L118
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CayleySpectrum.lean#L108-L118

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

theorem QEC.Coding.TannerLiftedProduct.cayleyGeneratorSum_action_mul_constantProjection
    (label : W → G) :
    cayleyRightRegularRepresentation.asAlgebraHom
          (cayleyGeneratorSum label) * cayleyConstantProjection =
      (Fintype.card W : ℂ) • cayleyConstantProjection := by sorry
