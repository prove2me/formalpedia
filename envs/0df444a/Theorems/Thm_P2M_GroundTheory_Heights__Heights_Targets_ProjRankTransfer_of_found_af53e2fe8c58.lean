-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRankTransfer_of_found_af53e2fe8c58
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ProjRankTransfer_of_found_af53e2fe8c58
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:44:58.550189+00:00
-- url     : https://prove2.me/theorems/aa4d5188-ad47-4cbf-9b4d-affd87e0508f
-- title:
--   P2 M Ground Theory Heights  Heights Targets Proj Rank Transfer of found af53e2fe8c58: P2 M Ground Theory Heights  Heights Targets Proj Rank Transfer of found af53e2fe8c58
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Proj Rank Transfer of found af53e2fe8c58 construction uses the P2 M Ground Theory Heights  Heights Targets Proj Rank Transfer of found af53e2fe8c58 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjRankTransfer.lean#L22-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjRankTransfer.lean#L22-L41

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

theorem P2M_GroundTheory_Heights__Heights_Targets_ProjRankTransfer_of_found_af53e2fe8c58 (hEq : ProjPotMassEq.Statement) (hPos : ProjPotMassPos.Statement)
    (hVan : ProjPotDensVanish.Statement) : ProjRankTransfer.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ProjRankTransfer».«of_found» := P2M_GroundTheory_Heights__Heights_Targets_ProjRankTransfer_of_found_af53e2fe8c58
