-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveFundamentalDomain
-- name    : QEC.Coding.TannerLiftedProduct.lpsEffectiveFundamentalDomain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:17:02.179231+00:00
-- url     : https://prove2.me/theorems/3ed2afde-fdd9-43e1-a720-e6c4014147da
-- title:
--   Tanner Lifted Product: lps Effective Fundamental Domain
-- statement:
--   Orbit coverage and proved null boundary give a genuine fundamental domain for the effective action.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularFundamentalDomain.lean#L128-L145
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularFundamentalDomain.lean#L128-L145

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

theorem QEC.Coding.TannerLiftedProduct.lpsEffectiveFundamentalDomain :
    IsFundamentalDomain lpsEffectiveModularGroup ModularGroup.fd volume := by sorry
