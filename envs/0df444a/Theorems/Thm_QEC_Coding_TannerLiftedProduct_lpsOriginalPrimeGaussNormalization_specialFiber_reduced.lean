-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeGaussNormalization_specialFiber_reduced
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeGaussNormalization_specialFiber_reduced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:48:39.518208+00:00
-- url     : https://prove2.me/theorems/555e7c57-907d-4e6f-9e0a-d6f74f02d5b2
-- title:
--   Tanner Lifted Product: lps Original Prime Gauss Normalization special Fiber reduced
-- statement:
--   The same actual prime-level normalization retains a reduced generic special fibre.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeGaussNormality.lean#L412-L459
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeGaussNormality.lean#L412-L459

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussLocalOrder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeKronecker
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeGaussNormality
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeGaussNormalization_specialFiber_reduced
    (p : ℕ) [Fact p.Prime] [NeZero p] :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalGaussAffineToGenerated p (Fact.out : p.Prime).pos p).toAlgebra
    letI : Algebra (LPSOriginalGaussBase p)
        (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos) :=
      ((lpsOriginalGaussAffineToGenerated p (Fact.out : p.Prime).pos p).comp
        (algebraMap (LPSOriginalGaussBase p)
          (LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p))).toAlgebra
    letI : CommRing (integralClosure (LPSOriginalGaussBase p)
        (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos)) := inferInstance
    letI : Ring (integralClosure (LPSOriginalGaussBase p)
        (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos)) := CommRing.toRing
    letI : Semiring (integralClosure (LPSOriginalGaussBase p)
        (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos)) :=
      (inferInstance : CommRing (integralClosure (LPSOriginalGaussBase p)
        (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos))).toCommSemiring.toSemiring
    IsReduced (integralClosure (LPSOriginalGaussBase p)
        (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos) ⧸
      (IsLocalRing.maximalIdeal (LPSOriginalGaussBase p)).map
        (algebraMap (LPSOriginalGaussBase p)
          (integralClosure (LPSOriginalGaussBase p)
            (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos)))) := by sorry
