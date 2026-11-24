-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_standardFlag_monotone_8be64143f027
-- name    : P2M_GroundTheory_Heights__Heights_standardFlag_monotone_8be64143f027
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:45:12.206469+00:00
-- url     : https://prove2.me/theorems/6be0e610-857d-43a9-b092-f15af0c98628
-- title:
--   P2 M Ground Theory Heights  Heights standard Flag monotone 8be64143f027: P2 M Ground Theory Heights  Heights standard Flag monotone 8be64143f027
-- statement:
--   The P2 M Ground Theory Heights  Heights standard Flag monotone 8be64143f027 construction uses the P2 M Ground Theory Heights  Heights standard Flag monotone 8be64143f027 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Slopes.lean#L166-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Slopes.lean#L166-L168

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField TensorProduct ComplexAt
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_standardFlag_monotone_8be64143f027 : Monotone (standardFlag K) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«standardFlag_monotone» := P2M_GroundTheory_Heights__Heights_standardFlag_monotone_8be64143f027
