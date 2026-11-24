-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_iSup_place_pos_10fee29093fa
-- name    : P2M_GroundTheory_Heights__Heights_iSup_place_pos_10fee29093fa
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:04:26.087177+00:00
-- url     : https://prove2.me/theorems/ecf2dc06-288b-4dcd-9089-fd3b51681fb6
-- title:
--   P2 M Ground Theory Heights  Heights i Sup place pos 10fee29093fa: P2 M Ground Theory Heights  Heights i Sup place pos 10fee29093fa
-- statement:
--   The P2 M Ground Theory Heights  Heights i Sup place pos 10fee29093fa construction uses the P2 M Ground Theory Heights  Heights i Sup place pos 10fee29093fa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/FieldChange.lean#L129-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/FieldChange.lean#L129-L133

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CardEmbeddingsRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FieldChange
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
open NumberField Module
noncomputable section
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem P2M_GroundTheory_Heights__Heights_iSup_place_pos_10fee29093fa {F : Type*} [Field F] [NumberField F] {ι : Type*} [Finite ι] {y : ι → F}
    (hy : y ≠ 0) (w : FinitePlace F) : 0 < ⨆ i, w (y i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«iSup_place_pos» := P2M_GroundTheory_Heights__Heights_iSup_place_pos_10fee29093fa
