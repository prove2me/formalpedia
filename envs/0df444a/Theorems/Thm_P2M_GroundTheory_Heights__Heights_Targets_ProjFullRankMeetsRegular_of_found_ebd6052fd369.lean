-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjFullRankMeetsRegular_of_found_ebd6052fd369
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ProjFullRankMeetsRegular_of_found_ebd6052fd369
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:47:12.774913+00:00
-- url     : https://prove2.me/theorems/07da5e56-b27a-59e2-a33f-029c30d83b3f
-- title:
--   P2 M Ground Theory Heights  Heights Targets Proj Full Rank Meets Regular of found ebd6052fd369: P2 M Ground Theory Heights  Heights Targets Proj Full Rank Meets Regular of found ebd6052fd369
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Proj Full Rank Meets Regular of found ebd6052fd369 construction uses the P2 M Ground Theory Heights  Heights Targets Proj Full Rank Meets Regular of found ebd6052fd369 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjFullRankMeetsRegular.lean#L14-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjFullRankMeetsRegular.lean#L14-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjFullRankMeetsRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRankTransfer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjMaxRankRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjFullRankMeetsRegular
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

theorem P2M_GroundTheory_Heights__Heights_Targets_ProjFullRankMeetsRegular_of_found_ebd6052fd369 (hT : ProjRankTransfer.Statement)
    (hM : ProjMaxRankMeetsPsi0.Statement) (hR : ProjMaxRankRegular.Statement) :
    ProjFullRankMeetsRegular.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ProjFullRankMeetsRegular».«of_found» := P2M_GroundTheory_Heights__Heights_Targets_ProjFullRankMeetsRegular_of_found_ebd6052fd369
