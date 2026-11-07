-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeDilationGeneratedFunctionFieldQ_relfinrank
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeDilationGeneratedFunctionFieldQ_relfinrank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:00:17.643295+00:00
-- url     : https://prove2.me/theorems/7339c1e8-0dc7-46b2-b35b-d59a79e256ae
-- title:
--   Tanner Lifted Product: lps Original Prime Dilation Generated Function Field Q relfinrank
-- statement:
--   The second actual Hecke pullback has relative degree p+1, measured in its literal embedded image.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalHeckePullback.lean#L359-L377
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalHeckePullback.lean#L359-L377

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalLevelInclusion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalHeckePullback
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeDilationGeneratedFunctionFieldQ_relfinrank
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hNp : p.Coprime N)
    (h4N : 4 ∣ N) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    ((lpsOriginalGeneratedFunctionFieldQ N hN).toSubfield.map
      (lpsOriginalDilationFractionPullback p (Fact.out : p.Prime).pos).toRingHom).relfinrank
        (lpsOriginalGeneratedFunctionFieldQ (N*p)
          (Nat.mul_pos hN (Fact.out : p.Prime).pos)).toSubfield = p+1 := by sorry
