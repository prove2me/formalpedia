-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0Translate_integerPeriod
-- name    : QEC.Coding.TannerLiftedProduct.lpsGamma0Translate_integerPeriod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:20:34.546411+00:00
-- url     : https://prove2.me/theorems/ca2ba7c0-3c9a-4e61-b3a6-8783596147a3
-- title:
--   Tanner Lifted Product: lps Gamma0 Translate integer Period
-- statement:
--   Every integral coset translate at Gamma0(N) has the common strict period N.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCongruenceSturm.lean#L20-L41
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCongruenceSturm.lean#L20-L41

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFourierPeriodChange
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceSturm
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold Pointwise

theorem QEC.Coding.TannerLiftedProduct.lpsGamma0Translate_integerPeriod (N : ℕ) (ρ : SL(2,ℤ)) :
    (N:ℝ)∈(ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ ρ)⁻¹ •
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))).strictPeriods := by sorry
