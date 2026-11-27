-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjFullRankDense_of_found_ede29b385614
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ProjFullRankDense_of_found_ede29b385614
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:40:57.363942+00:00
-- url     : https://prove2.me/theorems/450c29f5-e021-5141-b011-4a5af9d9b31a
-- title:
--   P2 M Ground Theory Heights  Heights Targets Proj Full Rank Dense of found ede29b385614: P2 M Ground Theory Heights  Heights Targets Proj Full Rank Dense of found ede29b385614
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Proj Full Rank Dense of found ede29b385614 construction uses the P2 M Ground Theory Heights  Heights Targets Proj Full Rank Dense of found ede29b385614 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjFullRankDense.lean#L12-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjFullRankDense.lean#L12-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegularClosureOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjFullRankMeetsRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjFullRankDense
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

theorem P2M_GroundTheory_Heights__Heights_Targets_ProjFullRankDense_of_found_ede29b385614 (hOpen : ProjRegularClosureOpen.Statement)
    (hMeet : ProjFullRankMeetsRegular.Statement) : ProjFullRankDense.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ProjFullRankDense».«of_found» := P2M_GroundTheory_Heights__Heights_Targets_ProjFullRankDense_of_found_ede29b385614
