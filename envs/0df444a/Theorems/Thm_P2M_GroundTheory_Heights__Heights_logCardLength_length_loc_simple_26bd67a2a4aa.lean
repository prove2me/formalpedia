-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_logCardLength_length_loc_simple_26bd67a2a4aa
-- name    : P2M_GroundTheory_Heights__Heights_logCardLength_length_loc_simple_26bd67a2a4aa
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:47:17.969802+00:00
-- url     : https://prove2.me/theorems/29b57596-7d48-4945-8d78-a3535e05101b
-- title:
--   P2 M Ground Theory Heights  Heights log Card Length length loc simple 26bd67a2a4aa: P2 M Ground Theory Heights  Heights log Card Length length loc simple 26bd67a2a4aa
-- statement:
--   The P2 M Ground Theory Heights  Heights log Card Length length loc simple 26bd67a2a4aa construction uses the P2 M Ground Theory Heights  Heights log Card Length length loc simple 26bd67a2a4aa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLogCardLength.lean#L52-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLogCardLength.lean#L52-L95

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLogCardLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLogCardLength
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
noncomputable section
open GroundTheory.Heights₂.Heights.logCardLength
open Module
variable (R : Type) [CommRing R]
variable {R}

theorem P2M_GroundTheory_Heights__Heights_logCardLength_length_loc_simple_26bd67a2a4aa (M : Type) [AddCommGroup M] [Module R M] [IsSimpleModule R M]
    (I : Ideal R) (hI : I.IsMaximal) (hkill : ∀ a ∈ I, ∀ x : M, a • x = 0)
    (m : Ideal R) [hm : m.IsPrime] :
    Module.length (Localization.AtPrime m) (LocalizedModule m.primeCompl M) =
      if m = I then 1 else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«logCardLength».«length_loc_simple» := P2M_GroundTheory_Heights__Heights_logCardLength_length_loc_simple_26bd67a2a4aa
