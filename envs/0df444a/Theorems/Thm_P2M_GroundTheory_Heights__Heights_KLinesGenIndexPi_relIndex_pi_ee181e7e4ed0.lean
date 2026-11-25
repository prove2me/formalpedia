-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesGenIndexPi_relIndex_pi_ee181e7e4ed0
-- name    : P2M_GroundTheory_Heights__Heights_KLinesGenIndexPi_relIndex_pi_ee181e7e4ed0
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:26:44.772532+00:00
-- url     : https://prove2.me/theorems/e27e8295-6132-491a-ae84-64058ed097c9
-- title:
--   P2 M Ground Theory Heights  Heights KLines Gen Index Pi rel Index pi ee181e7e4ed0: P2 M Ground Theory Heights  Heights KLines Gen Index Pi rel Index pi ee181e7e4ed0
-- statement:
--   The P2 M Ground Theory Heights  Heights KLines Gen Index Pi rel Index pi ee181e7e4ed0 construction uses the P2 M Ground Theory Heights  Heights KLines Gen Index Pi rel Index pi ee181e7e4ed0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesGenIndexPi.lean#L31-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesGenIndexPi.lean#L31-L39

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

theorem P2M_GroundTheory_Heights__Heights_KLinesGenIndexPi_relIndex_pi_ee181e7e4ed0 [Fintype η] (H K : η → AddSubgroup G) :
    (AddSubgroup.pi Set.univ H).relIndex (AddSubgroup.pi Set.univ K) =
      ∏ i, (H i).relIndex (K i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KLinesGenIndexPi».«relIndex_pi» := P2M_GroundTheory_Heights__Heights_KLinesGenIndexPi_relIndex_pi_ee181e7e4ed0
