-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledInteriorChart_symm
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFilledInteriorChart_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:57:52.709202+00:00
-- url     : https://prove2.me/theorems/0e788f42-3312-4d3b-a466-e984186ac4c9
-- title:
--   Tanner Lifted Product: lps Original Filled Interior Chart symm
-- statement:
--   The lifted interior inverse is exactly the original quotient projection of ofComplex, with no new lift or orbit.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCharts.lean#L136-L152
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCharts.lean#L136-L152

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledTopology
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0Quotient
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCharts
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFilledInteriorChart_symm (N : ℕ) [NeZero N] (hN : 4∣N)
    (x : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) (z : ℂ) :
    letI := lpsOriginalFilledTopology N
    (lpsOriginalFilledInteriorChart N hN x).symm z=
      Sum.inl (Quotient.mk (MulAction.orbitRel
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
        (UpperHalfPlane.ofComplex z)) := by sorry
