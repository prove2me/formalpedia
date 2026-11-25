-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_latticeDual_ne_bot_143b76fb3f48
-- name    : P2M_GroundTheory_Heights__Heights_latticeDual_ne_bot_143b76fb3f48
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:47:22.43181+00:00
-- url     : https://prove2.me/theorems/c7d8c55b-f93a-48ee-837a-8ce44958e054
-- title:
--   P2 M Ground Theory Heights  Heights lattice Dual ne bot 143b76fb3f48: P2 M Ground Theory Heights  Heights lattice Dual ne bot 143b76fb3f48
-- statement:
--   The P2 M Ground Theory Heights  Heights lattice Dual ne bot 143b76fb3f48 construction uses the P2 M Ground Theory Heights  Heights lattice Dual ne bot 143b76fb3f48 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PDualBasisExists.lean#L56-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PDualBasisExists.lean#L56-L80

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PDualBasisExists
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
open NumberField Matrix
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_latticeDual_ne_bot_143b76fb3f48 {K : Type*} [Field K] [NumberField K] {r : ℕ} (F : HermLattice K (r + 1)) :
    ∃ ψ ∈ latticeDual F.lattice, ψ ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«latticeDual_ne_bot» := P2M_GroundTheory_Heights__Heights_latticeDual_ne_bot_143b76fb3f48
