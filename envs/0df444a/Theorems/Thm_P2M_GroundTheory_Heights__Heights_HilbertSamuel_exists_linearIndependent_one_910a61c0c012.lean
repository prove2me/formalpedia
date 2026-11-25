-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_exists_linearIndependent_one_910a61c0c012
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_exists_linearIndependent_one_910a61c0c012
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:20:01.859492+00:00
-- url     : https://prove2.me/theorems/01013fd3-fadb-4ac3-bee4-c2709e8a1bfd
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel exists linear Independent one 910a61c0c012: P2 M Ground Theory Heights  Heights Hilbert Samuel exists linear Independent one 910a61c0c012
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel exists linear Independent one 910a61c0c012 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel exists linear Independent one 910a61c0c012 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/NormFibreVecPosOfLinearIndependent.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/NormFibreVecPosOfLinearIndependent.lean#L20-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StandardLatticeVecIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ShortFamilyEquivSmallFamilyVec
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_NormFibreVecPosOfLinearIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open NumberField TensorProduct
noncomputable section
variable {K : Type} [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_exists_linearIndependent_one_910a61c0c012 (E : HermitianBundle.{0} K) (h : 0 < bundleRank E) :
    ∃ s : Fin 1 → E.carrier, LinearIndependent (𝓞 K) s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«exists_linearIndependent_one» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_exists_linearIndependent_one_910a61c0c012
