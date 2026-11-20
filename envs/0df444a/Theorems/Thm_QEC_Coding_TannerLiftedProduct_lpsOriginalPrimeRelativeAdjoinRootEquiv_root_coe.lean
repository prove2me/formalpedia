-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeRelativeAdjoinRootEquiv_root_coe
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeRelativeAdjoinRootEquiv_root_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:18:45.867651+00:00
-- url     : https://prove2.me/theorems/fd7e668f-1853-4375-8a5e-0c11ef345a76
-- title:
--   Tanner Lifted Product: lps Original Prime Relative Adjoin Root Equiv root coe
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Prime Relative Adjoin Root Equiv root coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeRelativeMinpoly.lean#L176-L203
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeRelativeMinpoly.lean#L176-L203

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeIntegralHeckeRelation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelFunctionField
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeRelativeMinpoly
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeRelativeAdjoinRootEquiv_root_coe
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    ((lpsOriginalPrimeRelativeAdjoinRootEquiv N p hNp h4N hN
      (AdjoinRoot.root (lpsOriginalPrimeRelativeModularPolynomial N p hN
        (Fact.out : p.Prime).pos)) : lpsOriginalGeneratedFunctionFieldQ (N*p)
          (Nat.mul_pos hN (Fact.out : p.Prime).pos)) :
            LPSOriginalHolomorphicFractionField) =
      lpsOriginalJNInFractionField (N*p)
        (Nat.mul_pos hN (Fact.out : p.Prime).pos) := by sorry
