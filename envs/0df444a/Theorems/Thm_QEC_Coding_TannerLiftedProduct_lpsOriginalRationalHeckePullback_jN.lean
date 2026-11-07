-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalHeckePullback_jN
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRationalHeckePullback_jN
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T03:56:44.901283+00:00
-- url     : https://prove2.me/theorems/4d1c0471-31aa-4d2d-949e-a365da6d1fdc
-- title:
--   Tanner Lifted Product: lps Original Rational Hecke Pullback j N
-- statement:
--   The restricted second Hecke map really sends the second generator j_N to j_Np.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalHeckePullback.lean#L435-L446
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalHeckePullback.lean#L435-L446

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalLevelInclusion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalHeckePullback
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRationalHeckePullback_jN (N p : ℕ) [NeZero N] [NeZero p]
    (hN : 0 < N) (hp : 0 < p) (h4N : 4 ∣ N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    ((lpsOriginalRationalHeckePullback N p hN hp h4N
      ⟨lpsOriginalJNInFractionField N hN,
        IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)⟩ :
        lpsOriginalGeneratedFunctionFieldQ (N*p) (Nat.mul_pos hN hp)) :
          LPSOriginalHolomorphicFractionField) =
            lpsOriginalJNInFractionField (N*p) (Nat.mul_pos hN hp) := by sorry
