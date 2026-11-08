-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_cayleyGeneratorSum_action
-- name    : QEC.Coding.TannerLiftedProduct.cayleyGeneratorSum_action
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:11:40.865544+00:00
-- url     : https://prove2.me/theorems/1d50781e-2ff1-4025-9221-f93198516ab3
-- title:
--   Tanner Lifted Product: cayley Generator Sum action
-- statement:
--   Acting by the generator sum in the right regular representation is the
--   unnormalized Cayley adjacency operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CayleySpectrum.lean#L71-L77
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CayleySpectrum.lean#L71-L77

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

theorem QEC.Coding.TannerLiftedProduct.cayleyGeneratorSum_action
    (label : W → G) (f : G → ℂ) (g : G) :
    (cayleyRightRegularRepresentation.asAlgebraHom
        (cayleyGeneratorSum label) f) g =
      cayleyRightTranslationSum label f g := by sorry
