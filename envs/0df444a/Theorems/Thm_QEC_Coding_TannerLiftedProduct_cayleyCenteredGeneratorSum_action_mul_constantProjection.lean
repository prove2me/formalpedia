-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_cayleyCenteredGeneratorSum_action_mul_constantProjection
-- name    : QEC.Coding.TannerLiftedProduct.cayleyCenteredGeneratorSum_action_mul_constantProjection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:16:15.499911+00:00
-- url     : https://prove2.me/theorems/9eda25ce-50e9-4c25-9a48-871a4470d4b8
-- title:
--   Tanner Lifted Product: cayley Centered Generator Sum action mul constant Projection
-- statement:
--   Centered Cayley adjacency annihilates the constant projection on the
--   right.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CayleySpectrum.lean#L237-L245
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CayleySpectrum.lean#L237-L245

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

theorem QEC.Coding.TannerLiftedProduct.cayleyCenteredGeneratorSum_action_mul_constantProjection
    (label : W → G) :
    cayleyRightRegularRepresentation.asAlgebraHom
          (cayleyCenteredGeneratorSum label) * cayleyConstantProjection =
      0 := by sorry
