-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0QuotientFunc_analytic
-- name    : QEC.Coding.TannerLiftedProduct.lpsGamma0QuotientFunc_analytic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:20:46.258818+00:00
-- url     : https://prove2.me/theorems/4ed77300-e0f0-4328-a329-e16f7f3fa449
-- title:
--   Tanner Lifted Product: lps Gamma0 Quotient Func analytic
-- statement:
--   Every actual Gamma0(N) quotient slash component is analytic at the common N-width cusp.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCongruenceSturm.lean#L81-L92
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCongruenceSturm.lean#L81-L92

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFourierPeriodChange
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceSturm
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold Pointwise

theorem QEC.Coding.TannerLiftedProduct.lpsGamma0QuotientFunc_analytic (N : ℕ) [NeZero N] (k : ℤ)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    (q : 𝒮ℒ ⧸ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) :
    AnalyticAt ℂ (UpperHalfPlane.cuspFunction (N:ℝ) (SlashInvariantForm.quotientFunc f q)) 0 := by sorry
