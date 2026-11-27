-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitCenterZero_proof_f29a9d7c5910
-- name    : P2M_GroundTheory_Heights__Heights_OrbitCenterZero_proof_f29a9d7c5910
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:37:36.626703+00:00
-- url     : https://prove2.me/theorems/45f2780a-53ee-597c-a568-31bc2ba57430
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Center Zero proof f29a9d7c5910: P2 M Ground Theory Heights  Heights Orbit Center Zero proof f29a9d7c5910
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Center Zero proof f29a9d7c5910 construction uses the P2 M Ground Theory Heights  Heights Orbit Center Zero proof f29a9d7c5910 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitCenterZero.lean#L13-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitCenterZero.lean#L13-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenterZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenterLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenterMemIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PHeightRecR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCenterZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HeightRecR_proof_a841a96c8521

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
open ReciprocityTheory.ChartRestriction.G NumberField

theorem P2M_GroundTheory_Heights__Heights_OrbitCenterZero_proof_f29a9d7c5910 (hLe : OrbitCenterLe.Statement)
    (hIff : OrbitCenterMemIff.Statement) (hDiv : OrbitCenterDivSupp.Statement) :
    OrbitCenterZero.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitCenterZero».«proof» := P2M_GroundTheory_Heights__Heights_OrbitCenterZero_proof_f29a9d7c5910
