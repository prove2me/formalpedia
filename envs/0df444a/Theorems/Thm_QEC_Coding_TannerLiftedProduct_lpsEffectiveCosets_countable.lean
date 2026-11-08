-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveCosets_countable
-- name    : QEC.Coding.TannerLiftedProduct.lpsEffectiveCosets_countable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:17:31.979334+00:00
-- url     : https://prove2.me/theorems/e9f4b7ea-0252-4a0c-8b99-effd8e0eb243
-- title:
--   Tanner Lifted Product: lps Effective Cosets countable
-- statement:
--   Every coset space of the actual effective modular group is countable.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularFundamentalDomain.lean#L226-L228
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularFundamentalDomain.lean#L226-L228

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

theorem QEC.Coding.TannerLiftedProduct.lpsEffectiveCosets_countable (H : Subgroup lpsEffectiveModularGroup) :
    Countable (lpsEffectiveModularGroup ⧸ H) := by sorry
