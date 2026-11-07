-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspProjection_openRange
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspProjection_openRange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:35:42.447109+00:00
-- url     : https://prove2.me/theorems/eca5e9d5-5a6b-42ef-93bc-ab70caf840db
-- title:
--   Tanner Lifted Product: lps Original Cusp Projection open Range
-- statement:
--   The actual cusp neighborhood is an OPEN subspace of the original quotient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspNeighborhoods.lean#L272-L274
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspNeighborhoods.lean#L272-L274

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspWidths
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Homeomorph.Quotient
import Mathlib.Topology.Maps.Strict.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspNeighborhoods
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspProjection_openRange (N : ℕ) (ρ : SL(2,ℤ)) :
    IsOpen (Set.range (lpsOriginalCuspProjection N ρ)) := by sorry
