-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Avoid_minor__Multi_78e0f06a3ccb
-- name    : P2M_GlobalTheory_Avoid_minor__Multi_78e0f06a3ccb
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:05:27.192268+00:00
-- url     : https://prove2.me/theorems/68d48b41-7f17-498c-a0e4-c2b73c148c70
-- title:
--   P2 M Global Theory Avoid minor  Multi 78e0f06a3ccb: P2 M Global Theory Avoid minor  Multi 78e0f06a3ccb
-- statement:
--   The P2 M Global Theory Avoid minor  Multi 78e0f06a3ccb construction uses the P2 M Global Theory Avoid minor  Multi 78e0f06a3ccb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisMapOfLiftBaseChangeSurjective.lean#L149-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisMapOfLiftBaseChangeSurjective.lean#L149-L153

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisMapOfLiftBaseChangeSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Function
open scoped TensorProduct Pointwise
open GlobalTheory
open GlobalTheory.Avoid
open exteriorPower

theorem P2M_GlobalTheory_Avoid_minor__Multi_78e0f06a3ccb {R V ι : Type*} [CommRing R] [AddCommGroup V] [Module R V] [LinearOrder ι]
    (c : ι → Dual R V) {r : ℕ} (J : Set.powersetCard ι r) (v : Fin r → V) :
    pairingDual R V r (ιMulti_family R r c J) (ιMulti R r v) =
      (Matrix.of fun i j => c (Set.powersetCard.ofFinEmbEquiv.symm J j) (v i)).det := by sorry

alias «GlobalTheory».«Avoid».«minor_ιMulti» := P2M_GlobalTheory_Avoid_minor__Multi_78e0f06a3ccb
