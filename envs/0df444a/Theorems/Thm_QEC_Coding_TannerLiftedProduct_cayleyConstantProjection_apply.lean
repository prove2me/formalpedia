-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_cayleyConstantProjection_apply
-- name    : QEC.Coding.TannerLiftedProduct.cayleyConstantProjection_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:11:21.488421+00:00
-- url     : https://prove2.me/theorems/4281a661-f05a-4912-9952-7a074e1f25d5
-- title:
--   Tanner Lifted Product: cayley Constant Projection apply
-- statement:
--   The Tanner Lifted Product construction uses the cayley Constant Projection apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CayleySpectrum.lean#L90-L94
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CayleySpectrum.lean#L90-L94

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

theorem QEC.Coding.TannerLiftedProduct.cayleyConstantProjection_apply
    (f : G → ℂ) (g : G) :
    cayleyConstantProjection f g =
      (Fintype.card G : ℂ)⁻¹ * ∑ h, f h := by sorry
