-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_sum_unit_perm_2a06cd6a3a93
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_sum_unit_perm_2a06cd6a3a93
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:28:25.83738+00:00
-- url     : https://prove2.me/theorems/5f52fc9b-b640-4616-b0ed-4a7c6086e609
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free sum unit perm 2a06cd6a3a93: P2 M Ground Theory Heights  Heights Lower Bound Free sum unit perm 2a06cd6a3a93
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free sum unit perm 2a06cd6a3a93 construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free sum unit perm 2a06cd6a3a93 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/PermFinTwoUniv.lean#L72-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/PermFinTwoUniv.lean#L72-L76

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_PermFinTwoUniv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_sum_unit_perm_2a06cd6a3a93 {M : Type*} [AddCommMonoid M] (g : (Unit → Equiv.Perm (Fin 2)) → M) :
    ∑ w, g w = g (fun _ => 1) + g (fun _ => Equiv.swap 0 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«sum_unit_perm» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_sum_unit_perm_2a06cd6a3a93
