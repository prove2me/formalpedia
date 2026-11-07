-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJ_interior_analytic
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJ_interior_analytic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:06:38.924011+00:00
-- url     : https://prove2.me/theorems/ed7ecc91-ed31-46fe-80ab-d7d67618c56a
-- title:
--   Tanner Lifted Product: lps Original Filled J interior analytic
-- statement:
--   Analyticity in every target point of every actual original interior chart; used by nonzero cusp overlaps and all-chart meromorphy.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularFunction.lean#L312-L327
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularFunction.lean#L312-L327

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledConnected
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.Analysis.Meromorphic.Order
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJ_interior_analytic (N : ℕ) [NeZero N] (hN : 4∣N)
    (x : MulAction.orbitRel.Quotient (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
    (z : ℂ) (hz : z∈(lpsOriginalFilledInteriorChart N hN x).target) :
    letI := lpsOriginalFilledTopology N
    AnalyticAt ℂ (fun w : ℂ => lpsOriginalFilledJ N
      ((lpsOriginalFilledInteriorChart N hN x).symm w)) z := by sorry
