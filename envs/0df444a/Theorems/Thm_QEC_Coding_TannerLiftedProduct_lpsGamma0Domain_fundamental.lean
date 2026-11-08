-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0Domain_fundamental
-- name    : QEC.Coding.TannerLiftedProduct.lpsGamma0Domain_fundamental
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:20:29.211033+00:00
-- url     : https://prove2.me/theorems/60c7f90f-1dad-44e6-8ddd-1f485c89044a
-- title:
--   Tanner Lifted Product: lps Gamma0 Domain fundamental
-- statement:
--   The actual effective Gamma0 subgroup has its proved inverse-coset fundamental domain.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularFundamentalDomain.lean#L291-L294
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularFundamentalDomain.lean#L291-L294

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

theorem QEC.Coding.TannerLiftedProduct.lpsGamma0Domain_fundamental (N : ℕ) :
    IsFundamentalDomain (lpsEffectiveGamma0 N)
      (lpsCongruenceDomain (lpsEffectiveGamma0 N)) volume := by sorry
