-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_holomorphic_eq_const
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilled_holomorphic_eq_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:00:49.966892+00:00
-- url     : https://prove2.me/theorems/ddbcfab5-d73d-40a6-a49a-1481e6d46100
-- title:
--   Tanner Lifted Product: lps Original Filled holomorphic eq const
-- statement:
--   Every global holomorphic complex function on this same compact connected curve is constant; used to exclude a holomorphic extension of j.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledConnected.lean#L63-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledConnected.lean#L63-L74

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
import Mathlib.Geometry.Manifold.Complex
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.ClusterPt
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledConnected
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilled_holomorphic_eq_const (N : ℕ) [NeZero N] (hN : 4∣N)
    (f : LPSOriginalFilledCurve N → ℂ)
    (hf : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    ∃ c : ℂ, f=Function.const (LPSOriginalFilledCurve N) c := by sorry
