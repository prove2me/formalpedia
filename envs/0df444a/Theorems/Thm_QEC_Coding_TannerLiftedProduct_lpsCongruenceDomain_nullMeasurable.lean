-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCongruenceDomain_nullMeasurable
-- name    : QEC.Coding.TannerLiftedProduct.lpsCongruenceDomain_nullMeasurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:19:21.468196+00:00
-- url     : https://prove2.me/theorems/d9caefd1-7ab5-4b84-bf4d-c31b813711b9
-- title:
--   Tanner Lifted Product: lps Congruence Domain null Measurable
-- statement:
--   The actual inverse-coset union is null measurable for hyperbolic volume.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularFundamentalDomain.lean#L235-L240
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularFundamentalDomain.lean#L235-L240

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

theorem QEC.Coding.TannerLiftedProduct.lpsCongruenceDomain_nullMeasurable (H : Subgroup lpsEffectiveModularGroup) :
    NullMeasurableSet (lpsCongruenceDomain H) volume := by sorry
