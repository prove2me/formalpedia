-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQExpansion_prod
-- name    : QEC.Coding.TannerLiftedProduct.lpsQExpansion_prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:20:33.420713+00:00
-- url     : https://prove2.me/theorems/f7431bb9-5322-4d2a-8d43-7932350c1b3e
-- title:
--   Tanner Lifted Product: lps QExpansion prod
-- statement:
--   The actual Fourier expansion of an analytic finite product is the product of the expansions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCongruenceSturm.lean#L67-L78
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCongruenceSturm.lean#L67-L78

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFourierPeriodChange
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceSturm
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold Pointwise

theorem QEC.Coding.TannerLiftedProduct.lpsQExpansion_prod {ι : Type*} (h : ℝ) (s : Finset ι) (F : ι→ℍ→ℂ)
    (ha : ∀i∈s,AnalyticAt ℂ (UpperHalfPlane.cuspFunction h (F i)) 0) :
    UpperHalfPlane.qExpansion h (∏i∈s,F i)=∏i∈s,UpperHalfPlane.qExpansion h (F i) := by sorry
