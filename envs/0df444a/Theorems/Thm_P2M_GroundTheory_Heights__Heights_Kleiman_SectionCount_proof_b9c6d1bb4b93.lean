-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_proof_b9c6d1bb4b93
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_proof_b9c6d1bb4b93
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T06:32:56.220355+00:00
-- url     : https://prove2.me/theorems/dc01e862-0999-4ea1-9c4f-557f59b3015c
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Section Count proof b9c6d1bb4b93: P2 M Ground Theory Heights  Heights Kleiman Section Count proof b9c6d1bb4b93
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Section Count proof b9c6d1bb4b93 construction uses the P2 M Ground Theory Heights  Heights Kleiman Section Count proof b9c6d1bb4b93 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCount.lean#L12-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCount.lean#L12-L48

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountTopSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open Filter
universe u w

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_proof_b9c6d1bb4b93 (hT : SectionCount.Top.Statement.{u, w})
    (hD : SectionCount.Drop.Statement.{u, w}) : SectionCount.Statement.{u, w} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionCount».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_proof_b9c6d1bb4b93
