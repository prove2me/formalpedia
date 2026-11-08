-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_cayleyRightRegularRepresentation_apply
-- name    : QEC.Coding.TannerLiftedProduct.cayleyRightRegularRepresentation_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:11:14.338587+00:00
-- url     : https://prove2.me/theorems/f4cacc57-9dd3-4839-9cb9-f8bfec124f65
-- title:
--   Tanner Lifted Product: cayley Right Regular Representation apply
-- statement:
--   The Tanner Lifted Product construction uses the cayley Right Regular Representation apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CayleySpectrum.lean#L42-L44
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CayleySpectrum.lean#L42-L44

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

theorem QEC.Coding.TannerLiftedProduct.cayleyRightRegularRepresentation_apply
    (s g : G) (f : G → ℂ) :
    cayleyRightRegularRepresentation s f g = f (g * s) := by sorry

attribute [defeq] QEC.Coding.TannerLiftedProduct.cayleyRightRegularRepresentation_apply
