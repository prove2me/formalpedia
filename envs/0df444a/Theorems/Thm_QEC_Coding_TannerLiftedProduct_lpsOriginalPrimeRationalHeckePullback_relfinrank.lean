-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeRationalHeckePullback_relfinrank
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeRationalHeckePullback_relfinrank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:54:00.514862+00:00
-- url     : https://prove2.me/theorems/3a18c8ba-b90c-4513-8f7a-f51e2ae54d0a
-- title:
--   Tanner Lifted Product: lps Original Prime Rational Hecke Pullback relfinrank
-- statement:
--   The second genuine original rational Hecke map has image-relative degree p+1.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalHeckePullback.lean#L469-L480
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalHeckePullback.lean#L469-L480

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalLevelInclusion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalHeckePullback
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeRationalHeckePullback_relfinrank
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hNp : p.Coprime N)
    (h4N : 4 ∣ N) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (((lpsOriginalGeneratedFunctionFieldQ (N*p)
      (Nat.mul_pos hN (Fact.out : p.Prime).pos)).toSubfield.subtype.comp
      (lpsOriginalRationalHeckePullback N p hN (Fact.out : p.Prime).pos h4N)).fieldRange).relfinrank
        (lpsOriginalGeneratedFunctionFieldQ (N*p)
          (Nat.mul_pos hN (Fact.out : p.Prime).pos)).toSubfield = p+1 := by sorry
