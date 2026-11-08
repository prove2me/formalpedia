-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalHeckePullback_j
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRationalHeckePullback_j
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:53:20.77755+00:00
-- url     : https://prove2.me/theorems/d4a2d32c-960a-4e42-87a8-f1472e4c9342
-- title:
--   Tanner Lifted Product: lps Original Rational Hecke Pullback j
-- statement:
--   The restricted second Hecke map really sends the first generator j to j_p.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalHeckePullback.lean#L423-L432
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalHeckePullback.lean#L423-L432

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalLevelInclusion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalHeckePullback
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRationalHeckePullback_j (N p : ℕ) [NeZero N] [NeZero p]
    (hN : 0 < N) (hp : 0 < p) (h4N : 4 ∣ N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    ((lpsOriginalRationalHeckePullback N p hN hp h4N
      ⟨lpsOriginalJInFractionField, lpsOriginalJInFractionField_mem_generatedQ N hN⟩ :
        lpsOriginalGeneratedFunctionFieldQ (N*p) (Nat.mul_pos hN hp)) :
          LPSOriginalHolomorphicFractionField) = lpsOriginalJNInFractionField p hp := by sorry
