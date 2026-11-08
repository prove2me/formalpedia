-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_trace_cayleyConstantProjection
-- name    : QEC.Coding.TannerLiftedProduct.trace_cayleyConstantProjection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:11:52.941191+00:00
-- url     : https://prove2.me/theorems/5ca6eea0-60e2-4233-ac81-a15032b2fc4a
-- title:
--   Tanner Lifted Product: trace cayley Constant Projection
-- statement:
--   The averaging projection onto constants has trace one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CayleySpectrum.lean#L197-L204
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CayleySpectrum.lean#L197-L204

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

theorem QEC.Coding.TannerLiftedProduct.trace_cayleyConstantProjection :
    LinearMap.trace ℂ (G → ℂ) (cayleyConstantProjection (G := G)) = 1 := by sorry
