-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalHeckePullback_fieldRange
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRationalHeckePullback_fieldRange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:00:11.961043+00:00
-- url     : https://prove2.me/theorems/36504d8f-3afd-4f9f-acc8-5a108af28bb6
-- title:
--   Tanner Lifted Product: lps Original Rational Hecke Pullback field Range
-- statement:
--   The actual restricted Hecke map has exactly the proved ambient dilation image.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalHeckePullback.lean#L449-L466
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalHeckePullback.lean#L449-L466

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalLevelInclusion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalHeckePullback
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRationalHeckePullback_fieldRange (N p : ℕ) [NeZero N] [NeZero p]
    (hN : 0 < N) (hp : 0 < p) (h4N : 4 ∣ N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    ((lpsOriginalGeneratedFunctionFieldQ (N*p) (Nat.mul_pos hN hp)).toSubfield.subtype.comp
      (lpsOriginalRationalHeckePullback N p hN hp h4N)).fieldRange =
        (lpsOriginalGeneratedFunctionFieldQ N hN).toSubfield.map
          (lpsOriginalDilationFractionPullback p hp).toRingHom := by sorry
