-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalHeckePullback_coe
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRationalHeckePullback_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:59:28.745838+00:00
-- url     : https://prove2.me/theorems/677d9f08-df62-4102-8450-eec771d9004d
-- title:
--   Tanner Lifted Product: lps Original Rational Hecke Pullback coe
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Rational Hecke Pullback coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalHeckePullback.lean#L397-L406
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalHeckePullback.lean#L397-L406

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalLevelInclusion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalHeckePullback
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRationalHeckePullback_coe (N p : ℕ) [NeZero N] [NeZero p]
    (hN : 0 < N) (hp : 0 < p) (h4N : 4 ∣ N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    ∀ x : lpsOriginalGeneratedFunctionFieldQ N hN,
      ((lpsOriginalRationalHeckePullback N p hN hp h4N x :
        lpsOriginalGeneratedFunctionFieldQ (N*p) (Nat.mul_pos hN hp)) :
          LPSOriginalHolomorphicFractionField) = lpsOriginalDilationFractionPullback p hp x := by sorry
