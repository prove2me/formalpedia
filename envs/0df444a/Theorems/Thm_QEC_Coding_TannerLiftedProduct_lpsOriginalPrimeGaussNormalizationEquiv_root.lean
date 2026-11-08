-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeGaussNormalizationEquiv_root
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeGaussNormalizationEquiv_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:48:19.692384+00:00
-- url     : https://prove2.me/theorems/28b6fda9-0010-48f5-89e4-369e986a8c8a
-- title:
--   Tanner Lifted Product: lps Original Prime Gauss Normalization Equiv root
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Prime Gauss Normalization Equiv root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeGaussNormality.lean#L378-L403
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeGaussNormality.lean#L378-L403

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeGaussNormalizationEquiv_root
    (p : ℕ) [Fact p.Prime] [NeZero p] :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalGaussAffineToGenerated p (Fact.out : p.Prime).pos p).toAlgebra
    letI : Algebra (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos) :=
      ((lpsOriginalGaussAffineToGenerated p (Fact.out : p.Prime).pos p).comp
        (algebraMap (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p))).toAlgebra
    ((lpsOriginalPrimeGaussNormalizationEquiv p
      (AdjoinRoot.root (lpsOriginalGaussPolynomial p (Fact.out : p.Prime).pos p))).val.val) =
      lpsOriginalJNInFractionField p (Fact.out : p.Prime).pos := by sorry
