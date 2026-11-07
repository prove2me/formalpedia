-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0Norm_order_commonWidth
-- name    : QEC.Coding.TannerLiftedProduct.lpsGamma0Norm_order_commonWidth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:20:53.829436+00:00
-- url     : https://prove2.me/theorems/9f133621-421e-4ae4-bd8c-099131d00f08
-- title:
--   Tanner Lifted Product: lps Gamma0 Norm order common Width
-- statement:
--   The identity coset gives a lower bound for the norm Fourier order at common width N.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCongruenceSturm.lean#L110-L123
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCongruenceSturm.lean#L110-L123

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFourierPeriodChange
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceSturm
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold Pointwise

theorem QEC.Coding.TannerLiftedProduct.lpsGamma0Norm_order_commonWidth (N : ℕ) [NeZero N] (k : ℤ)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) :
    (UpperHalfPlane.qExpansion (N:ℝ) f).order≤
      (UpperHalfPlane.qExpansion (N:ℝ) (ModularForm.norm 𝒮ℒ f)).order := by sorry
