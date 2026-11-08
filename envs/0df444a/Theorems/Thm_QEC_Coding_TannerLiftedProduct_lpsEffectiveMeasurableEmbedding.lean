-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveMeasurableEmbedding
-- name    : QEC.Coding.TannerLiftedProduct.lpsEffectiveMeasurableEmbedding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:20:19.744474+00:00
-- url     : https://prove2.me/theorems/6a2ddda7-b02e-45a3-b29e-f0ec9b2adc4f
-- title:
--   Tanner Lifted Product: lps Effective Measurable Embedding
-- statement:
--   Every effective modular permutation is a measurable embedding.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularFundamentalDomain.lean#L97-L106
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularFundamentalDomain.lean#L97-L106

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

theorem QEC.Coding.TannerLiftedProduct.lpsEffectiveMeasurableEmbedding (g : lpsEffectiveModularGroup) :
    MeasurableEmbedding (fun τ : ℍ => g • τ) := by sorry
