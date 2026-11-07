-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalLevelPhasePrime_comap
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalLevelPhasePrime_comap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:17:06.059196+00:00
-- url     : https://prove2.me/theorems/9f726057-d9f3-4082-83c5-18c292a993ce
-- title:
--   Tanner Lifted Product: lps Original Level Phase Prime comap
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Level Phase Prime comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspPhaseResidue.lean#L302-L307
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspPhaseResidue.lean#L302-L307

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.FieldTheory.KummerExtension
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspPhaseResidue
set_option autoImplicit false
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalLevelPhasePrime_isMaximal

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalLevelPhasePrime_comap
    (N : ℕ) (hN : 0 < N) (p : ℕ) (hp : p.Prime) :
    (lpsOriginalLevelPhasePrime N hN p hp).comap
      (algebraMap ℤ (lpsOriginalLevelPhaseRing N)) =
        RingHom.ker (Int.castRingHom (ZMod p)) := by sorry
