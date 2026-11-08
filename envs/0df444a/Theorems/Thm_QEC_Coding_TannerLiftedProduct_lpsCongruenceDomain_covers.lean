-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCongruenceDomain_covers
-- name    : QEC.Coding.TannerLiftedProduct.lpsCongruenceDomain_covers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:19:26.045963+00:00
-- url     : https://prove2.me/theorems/dc7725f4-b924-49ba-a6d3-bc65a6728e36
-- title:
--   Tanner Lifted Product: lps Congruence Domain covers
-- statement:
--   Every point has an actual subgroup translate in the inverse-coset union domain.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularFundamentalDomain.lean#L243-L257
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularFundamentalDomain.lean#L243-L257

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

theorem QEC.Coding.TannerLiftedProduct.lpsCongruenceDomain_covers (H : Subgroup lpsEffectiveModularGroup) (τ : ℍ) :
    ∃h : H,h • τ ∈ lpsCongruenceDomain H := by sorry
