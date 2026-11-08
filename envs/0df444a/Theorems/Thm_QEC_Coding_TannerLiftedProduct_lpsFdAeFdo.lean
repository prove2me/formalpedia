-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsFdAeFdo
-- name    : QEC.Coding.TannerLiftedProduct.lpsFdAeFdo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:19:14.687824+00:00
-- url     : https://prove2.me/theorems/0b29bc9e-eea0-45da-a24f-9b95e81368d7
-- title:
--   Tanner Lifted Product: lps Fd Ae Fdo
-- statement:
--   The actual closed and open modular domains agree almost everywhere.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularFundamentalDomain.lean#L63-L65
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularFundamentalDomain.lean#L63-L65

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

theorem QEC.Coding.TannerLiftedProduct.lpsFdAeFdo : ModularGroup.fd =ᵐ[volume] ModularGroup.fdo := by sorry
