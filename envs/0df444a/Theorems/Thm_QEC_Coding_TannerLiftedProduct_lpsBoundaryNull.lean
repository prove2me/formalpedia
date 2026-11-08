-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsBoundaryNull
-- name    : QEC.Coding.TannerLiftedProduct.lpsBoundaryNull
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:19:16.2187+00:00
-- url     : https://prove2.me/theorems/88ed3226-727d-4587-a3dc-0b76cca79717
-- title:
--   Tanner Lifted Product: lps Boundary Null
-- statement:
--   The circle and vertical-line boundary of the actual closed modular domain is hyperbolically null.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularFundamentalDomain.lean#L38-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularFundamentalDomain.lean#L38-L60

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

theorem QEC.Coding.TannerLiftedProduct.lpsBoundaryNull : (volume : Measure ℍ) (ModularGroup.fd \ ModularGroup.fdo) = 0 := by sorry
