-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalLevelPhaseMap_injectiveOnRoots
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalLevelPhaseMap_injectiveOnRoots
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:17:52.499991+00:00
-- url     : https://prove2.me/theorems/1c4bf098-1f11-4d96-b975-8155963daed5
-- title:
--   Tanner Lifted Product: lps Original Level Phase Map injective On Roots
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Level Phase Map injective On Roots property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspPhaseResidue.lean#L352-L371
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspPhaseResidue.lean#L352-L371

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
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalLevelPhaseResidue_field

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalLevelPhaseMap_injectiveOnRoots
    (N : ℕ) (hN : 0 < N) (K : Type*) [Field K]
    (φ : lpsOriginalLevelPhaseRing N →+* K) (hNK : (N : K) ≠ 0) :
    Set.InjOn φ {z : lpsOriginalLevelPhaseRing N | z^N = 1} := by sorry
