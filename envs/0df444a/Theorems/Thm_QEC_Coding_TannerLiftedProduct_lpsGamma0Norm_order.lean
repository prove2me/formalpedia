-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0Norm_order
-- name    : QEC.Coding.TannerLiftedProduct.lpsGamma0Norm_order
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:21:47.682497+00:00
-- url     : https://prove2.me/theorems/0acb1b55-98e1-4aab-a9c9-caa5dd138bae
-- title:
--   Tanner Lifted Product: lps Gamma0 Norm order
-- statement:
--   Cancel the positive integer width to compare the actual unit-width Fourier orders.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCongruenceSturm.lean#L126-L135
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCongruenceSturm.lean#L126-L135

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFourierPeriodChange
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceSturm
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold Pointwise

theorem QEC.Coding.TannerLiftedProduct.lpsGamma0Norm_order (N : ℕ) [NeZero N] (k : ℤ)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) :
    (UpperHalfPlane.qExpansion 1 f).order≤
      (UpperHalfPlane.qExpansion 1 (ModularForm.norm 𝒮ℒ f)).order := by sorry
