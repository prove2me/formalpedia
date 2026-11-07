-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspFunction_one
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspFunction_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:20:34.485459+00:00
-- url     : https://prove2.me/theorems/221c36b3-8558-4c97-8179-5b9d698c2ecb
-- title:
--   Tanner Lifted Product: lps Cusp Function one
-- statement:
--   The actual cusp function of the constant one function is constant one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCongruenceSturm.lean#L44-L49
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCongruenceSturm.lean#L44-L49

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFourierPeriodChange
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceSturm
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold Pointwise

theorem QEC.Coding.TannerLiftedProduct.lpsCuspFunction_one (h : ℝ) : UpperHalfPlane.cuspFunction h (1:ℍ→ℂ)=1 := by sorry
