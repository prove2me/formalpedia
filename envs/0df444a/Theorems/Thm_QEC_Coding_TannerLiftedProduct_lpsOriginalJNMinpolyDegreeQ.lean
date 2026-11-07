-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJNMinpolyDegreeQ
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJNMinpolyDegreeQ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:08:07.746452+00:00
-- url     : https://prove2.me/theorems/622aceee-e4a3-459b-b22b-15fdd783e2f4
-- title:
--   Tanner Lifted Product: lps Original JNMinpoly Degree Q
-- statement:
--   Exact rational minimal-polynomial degree from the proved SAME generated-field degree.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModularEquation.lean#L35-L43
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModularEquation.lean#L35-L43

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactFunctionFieldDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactStabilizer
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerQExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.Minpoly
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJNMinpolyDegreeQ (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (minpoly (FractionRing (Polynomial ℚ))
      (lpsOriginalJNInFractionField N hN)).natDegree =
      Nat.card (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) := by sorry
