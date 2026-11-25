-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRankTransfer_locallyConnectedSpace_b33ab8750658
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ProjRankTransfer_locallyConnectedSpace_b33ab8750658
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:42:56.755052+00:00
-- url     : https://prove2.me/theorems/f1a87e94-1221-526f-9887-78b49a55a1e0
-- title:
--   P2 M Ground Theory Heights  Heights Targets Proj Rank Transfer locally Connected Space b33ab8750658: P2 M Ground Theory Heights  Heights Targets Proj Rank Transfer locally Connected Space b33ab8750658
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Proj Rank Transfer locally Connected Space b33ab8750658 construction uses the P2 M Ground Theory Heights  Heights Targets Proj Rank Transfer locally Connected Space b33ab8750658 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjRankTransfer.lean#L13-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjRankTransfer.lean#L13-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRankTransfer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjPotMassPos
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjPotDensVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRankTransfer
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

theorem P2M_GroundTheory_Heights__Heights_Targets_ProjRankTransfer_locallyConnectedSpace_b33ab8750658 {e : ℕ} {X : Type*} [TopologicalSpace X]
    (A : FinHolAtlas e X) : LocallyConnectedSpace X := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ProjRankTransfer».«locallyConnectedSpace» := P2M_GroundTheory_Heights__Heights_Targets_ProjRankTransfer_locallyConnectedSpace_b33ab8750658
