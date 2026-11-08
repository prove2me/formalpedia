-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveGamma0_index
-- name    : QEC.Coding.TannerLiftedProduct.lpsEffectiveGamma0_index
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:19:16.75121+00:00
-- url     : https://prove2.me/theorems/ccf23409-ea30-4c1f-b022-309a6db59017
-- title:
--   Tanner Lifted Product: lps Effective Gamma0 index
-- statement:
--   Removing the ineffective center preserves the exact congruence index.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularFundamentalDomain.lean#L221-L223
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularFundamentalDomain.lean#L221-L223

import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.Modular
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Data.Countable.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularFundamentalDomain
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsEffectiveGamma0_index (N : ℕ) :
    (lpsEffectiveGamma0 N).index = (CongruenceSubgroup.Gamma0 N).index := by sorry
