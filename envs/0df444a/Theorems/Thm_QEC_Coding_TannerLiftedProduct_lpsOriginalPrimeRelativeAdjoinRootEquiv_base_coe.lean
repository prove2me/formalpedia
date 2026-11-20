-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeRelativeAdjoinRootEquiv_base_coe
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeRelativeAdjoinRootEquiv_base_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:20:05.135033+00:00
-- url     : https://prove2.me/theorems/8921a9bd-fa5c-40e0-b762-60a7cda8ef34
-- title:
--   Tanner Lifted Product: lps Original Prime Relative Adjoin Root Equiv base coe
-- statement:
--   The presentation sends every lower-level field coefficient to its actual inclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeRelativeMinpoly.lean#L223-L244
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeRelativeMinpoly.lean#L223-L244

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeIntegralHeckeRelation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelFunctionField
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeRelativeMinpoly
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeRelativeAdjoinRootEquiv_base_coe
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    ∀ c : lpsOriginalGeneratedFunctionFieldQ N hN,
    ((lpsOriginalPrimeRelativeAdjoinRootEquiv N p hNp h4N hN
      (algebraMap (lpsOriginalGeneratedFunctionFieldQ N hN)
        (AdjoinRoot (lpsOriginalPrimeRelativeModularPolynomial N p hN
          (Fact.out : p.Prime).pos)) c) : lpsOriginalGeneratedFunctionFieldQ (N*p)
            (Nat.mul_pos hN (Fact.out : p.Prime).pos)) :
              LPSOriginalHolomorphicFractionField) = c := by sorry
