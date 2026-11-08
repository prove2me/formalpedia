-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_trace_cayleyRightRegularRepresentation
-- name    : QEC.Coding.TannerLiftedProduct.trace_cayleyRightRegularRepresentation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:12:39.068205+00:00
-- url     : https://prove2.me/theorems/026bd4e8-03d5-42e5-a9db-35e4a12e2399
-- title:
--   Tanner Lifted Product: trace cayley Right Regular Representation
-- statement:
--   The trace of a right translation is the size of the group for the
--   identity translation and zero otherwise.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CayleySpectrum.lean#L148-L167
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CayleySpectrum.lean#L148-L167

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

theorem QEC.Coding.TannerLiftedProduct.trace_cayleyRightRegularRepresentation (s : G) :
    LinearMap.trace ℂ (G → ℂ)
        (cayleyRightRegularRepresentation (G := G) s) =
      if s = 1 then (Fintype.card G : ℂ) else 0 := by sorry
