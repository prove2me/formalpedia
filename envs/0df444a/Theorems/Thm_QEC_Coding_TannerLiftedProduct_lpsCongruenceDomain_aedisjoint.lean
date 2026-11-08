-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCongruenceDomain_aedisjoint
-- name    : QEC.Coding.TannerLiftedProduct.lpsCongruenceDomain_aedisjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:19:30.9672+00:00
-- url     : https://prove2.me/theorems/18b4336f-b535-40ff-ab5f-b21870be654e
-- title:
--   Tanner Lifted Product: lps Congruence Domain aedisjoint
-- statement:
--   Nonidentity subgroup translates of the actual inverse-coset domain are almost disjoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularFundamentalDomain.lean#L260-L279
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularFundamentalDomain.lean#L260-L279

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

theorem QEC.Coding.TannerLiftedProduct.lpsCongruenceDomain_aedisjoint (H : Subgroup lpsEffectiveModularGroup)
    (h : H) (hh : h ≠ 1) :
    AEDisjoint volume (h • lpsCongruenceDomain H) (lpsCongruenceDomain H) := by sorry
