-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHyperbolicNull
-- name    : QEC.Coding.TannerLiftedProduct.lpsHyperbolicNull
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:18:03.644001+00:00
-- url     : https://prove2.me/theorems/0cf02e73-6398-4dca-be21-0c23d690fde4
-- title:
--   Tanner Lifted Product: lps Hyperbolic Null
-- statement:
--   Ambient complex null sets pull back to null sets for the actual weighted hyperbolic volume.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularFundamentalDomain.lean#L21-L25
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularFundamentalDomain.lean#L21-L25

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

theorem QEC.Coding.TannerLiftedProduct.lpsHyperbolicNull {s : Set ℍ}
    (hs : (volume : Measure ℂ) (UpperHalfPlane.coe '' s) = 0) :
    (volume : Measure ℍ) s = 0 := by sorry
