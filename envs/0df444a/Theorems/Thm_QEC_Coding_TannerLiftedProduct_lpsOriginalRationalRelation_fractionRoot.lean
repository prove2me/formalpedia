-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalRelation_fractionRoot
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRationalRelation_fractionRoot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:08:44.759377+00:00
-- url     : https://prove2.me/theorems/6eba2ed7-a0f1-41d3-8b5d-5a3b6ae67c6b
-- title:
--   Tanner Lifted Product: lps Original Rational Relation fraction Root
-- statement:
--   Actual pointwise rational relation descends to an annihilator in the ambient fraction field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModularEquation.lean#L105-L150
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModularEquation.lean#L105-L150

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRationalRelation_fractionRoot
    (N : ℕ) [NeZero N] (hN : 0 < N) (Φ : Polynomial (Polynomial ℚ))
    (hroot : ∀ τ : ℍ,
      Φ.eval₂ ((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
        (Polynomial.mapRingHom (algebraMap ℚ ℂ))) (lpsOriginalJDilated N hN τ)=0) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    Polynomial.aeval (lpsOriginalJNInFractionField N hN)
      (Φ.map (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ))))=0 := by sorry
