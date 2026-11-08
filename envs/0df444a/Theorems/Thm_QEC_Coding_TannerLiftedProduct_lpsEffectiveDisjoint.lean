-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveDisjoint
-- name    : QEC.Coding.TannerLiftedProduct.lpsEffectiveDisjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:19:11.196294+00:00
-- url     : https://prove2.me/theorems/018a1f69-eed2-4059-b6e6-c14c24385da2
-- title:
--   Tanner Lifted Product: lps Effective Disjoint
-- statement:
--   A nonidentity effective permutation cannot overlap the open modular domain.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularFundamentalDomain.lean#L109-L125
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularFundamentalDomain.lean#L109-L125

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

theorem QEC.Coding.TannerLiftedProduct.lpsEffectiveDisjoint (g : lpsEffectiveModularGroup) (hg : g ≠ 1) :
    Disjoint (g • ModularGroup.fdo) ModularGroup.fdo := by sorry
