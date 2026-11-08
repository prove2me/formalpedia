-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCongruenceDomain_fundamental
-- name    : QEC.Coding.TannerLiftedProduct.lpsCongruenceDomain_fundamental
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:19:37.956292+00:00
-- url     : https://prove2.me/theorems/2b6e8dc2-f41e-4c6f-bfdf-5ba73ce3f300
-- title:
--   Tanner Lifted Product: lps Congruence Domain fundamental
-- statement:
--   The actual inverse-coset union is a genuine subgroup fundamental domain.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularFundamentalDomain.lean#L282-L288
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularFundamentalDomain.lean#L282-L288

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

theorem QEC.Coding.TannerLiftedProduct.lpsCongruenceDomain_fundamental (H : Subgroup lpsEffectiveModularGroup) :
    IsFundamentalDomain H (lpsCongruenceDomain H) volume := by sorry
