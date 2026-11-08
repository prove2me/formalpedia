-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0Domain_finiteIndex
-- name    : QEC.Coding.TannerLiftedProduct.lpsGamma0Domain_finiteIndex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:20:30.319911+00:00
-- url     : https://prove2.me/theorems/05f2b981-6908-4ee7-aed7-6492777e3c97
-- title:
--   Tanner Lifted Product: lps Gamma0 Domain finite Index
-- statement:
--   Every positive original Gamma0 level has finite index in the effective modular group.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularFundamentalDomain.lean#L297-L300
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularFundamentalDomain.lean#L297-L300

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

theorem QEC.Coding.TannerLiftedProduct.lpsGamma0Domain_finiteIndex (N : ℕ) [NeZero N] :
    (lpsEffectiveGamma0 N).FiniteIndex := by sorry
