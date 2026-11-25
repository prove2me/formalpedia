-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_logCardLength_term_simple_b0525ec75e65
-- name    : P2M_GroundTheory_Heights__Heights_logCardLength_term_simple_b0525ec75e65
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:48:36.470503+00:00
-- url     : https://prove2.me/theorems/f67aabb3-fe7f-4daa-8687-57dba3d1c9cf
-- title:
--   P2 M Ground Theory Heights  Heights log Card Length term simple b0525ec75e65: P2 M Ground Theory Heights  Heights log Card Length term simple b0525ec75e65
-- statement:
--   The P2 M Ground Theory Heights  Heights log Card Length term simple b0525ec75e65 construction uses the P2 M Ground Theory Heights  Heights log Card Length term simple b0525ec75e65 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLogCardLength.lean#L97-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLogCardLength.lean#L97-L106

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

theorem P2M_GroundTheory_Heights__Heights_logCardLength_term_simple_b0525ec75e65 (M : Type) [AddCommGroup M] [Module R M] [IsSimpleModule R M]
    (I : Ideal R) (hI : I.IsMaximal) (hkill : ∀ a ∈ I, ∀ x : M, a • x = 0)
    (hcard : Nat.card M = Nat.card (R ⧸ I)) (m : Ideal R) :
    term R M m = if m = I then Real.log (Nat.card M) else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«logCardLength».«term_simple» := P2M_GroundTheory_Heights__Heights_logCardLength_term_simple_b0525ec75e65
