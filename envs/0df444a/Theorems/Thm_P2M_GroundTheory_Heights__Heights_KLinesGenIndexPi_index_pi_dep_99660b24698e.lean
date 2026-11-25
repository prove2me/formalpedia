-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesGenIndexPi_index_pi_dep_99660b24698e
-- name    : P2M_GroundTheory_Heights__Heights_KLinesGenIndexPi_index_pi_dep_99660b24698e
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:26:36.168378+00:00
-- url     : https://prove2.me/theorems/4d5a3903-74c3-45cf-b14a-4cd2224832b2
-- title:
--   P2 M Ground Theory Heights  Heights KLines Gen Index Pi index pi dep 99660b24698e: P2 M Ground Theory Heights  Heights KLines Gen Index Pi index pi dep 99660b24698e
-- statement:
--   The P2 M Ground Theory Heights  Heights KLines Gen Index Pi index pi dep 99660b24698e construction uses the P2 M Ground Theory Heights  Heights KLines Gen Index Pi index pi dep 99660b24698e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesGenIndexPi.lean#L13-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesGenIndexPi.lean#L13-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesGenIndexPi
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
open GroundTheory.Heights₂.Heights.KLinesGenIndexPi
open AddSubgroup
variable {η : Type} {G : Type} [AddCommGroup G]

theorem P2M_GroundTheory_Heights__Heights_KLinesGenIndexPi_index_pi_dep_99660b24698e [Fintype η] {β : η → Type} [∀ i, AddCommGroup (β i)]
    (H : ∀ i, AddSubgroup (β i)) :
    (AddSubgroup.pi Set.univ H).index = ∏ i, (H i).index := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KLinesGenIndexPi».«index_pi_dep» := P2M_GroundTheory_Heights__Heights_KLinesGenIndexPi_index_pi_dep_99660b24698e
