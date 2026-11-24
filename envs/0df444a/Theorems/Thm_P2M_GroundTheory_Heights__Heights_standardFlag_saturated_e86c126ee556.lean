-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_standardFlag_saturated_e86c126ee556
-- name    : P2M_GroundTheory_Heights__Heights_standardFlag_saturated_e86c126ee556
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:31:36.571183+00:00
-- url     : https://prove2.me/theorems/998f33c8-d9a0-4f70-805f-9395ed2b9099
-- title:
--   P2 M Ground Theory Heights  Heights standard Flag saturated e86c126ee556: P2 M Ground Theory Heights  Heights standard Flag saturated e86c126ee556
-- statement:
--   The P2 M Ground Theory Heights  Heights standard Flag saturated e86c126ee556 construction uses the P2 M Ground Theory Heights  Heights standard Flag saturated e86c126ee556 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Slopes.lean#L170-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Slopes.lean#L170-L189

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

theorem P2M_GroundTheory_Heights__Heights_standardFlag_saturated_e86c126ee556 (i : Fin 3) :
    (HermitianBundle.standard K 2).Saturated (standardFlag K i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«standardFlag_saturated» := P2M_GroundTheory_Heights__Heights_standardFlag_saturated_e86c126ee556
