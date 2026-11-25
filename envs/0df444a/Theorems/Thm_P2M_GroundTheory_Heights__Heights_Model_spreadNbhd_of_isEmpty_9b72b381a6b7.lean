-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_spreadNbhd_of_isEmpty_9b72b381a6b7
-- name    : P2M_GroundTheory_Heights__Heights_Model_spreadNbhd_of_isEmpty_9b72b381a6b7
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:50:38.658953+00:00
-- url     : https://prove2.me/theorems/5df4ff57-781c-5188-91a9-55204d56632d
-- title:
--   P2 M Ground Theory Heights  Heights Model spread Nbhd of is Empty 9b72b381a6b7: P2 M Ground Theory Heights  Heights Model spread Nbhd of is Empty 9b72b381a6b7
-- statement:
--   The P2 M Ground Theory Heights  Heights Model spread Nbhd of is Empty 9b72b381a6b7 construction uses the P2 M Ground Theory Heights  Heights Model spread Nbhd of is Empty 9b72b381a6b7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PSpreadBundleNbhd.lean#L35-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PSpreadBundleNbhd.lean#L35-L48

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadNbhd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadStep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PSpreadBundleNbhd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
variable {X : Scheme.{0}}

theorem P2M_GroundTheory_Heights__Heights_Model_spreadNbhd_of_isEmpty_9b72b381a6b7 (f : X ⟶ SpecZ) (R : Type) [CommRing R] [IsEmpty (baseChange f R)]
    (E : (baseChange f R).Modules) :
    ∃ (W : X.Opens) (hW : Set.range (baseChangeMap f R) ⊆ Set.range W.ι)
      (E' : (W : Scheme.{0}).Modules), IsVectorBundle E' ∧
        Nonempty ((Scheme.Modules.pullback (toOpen f R W hW)).obj E' ≅ E) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«spreadNbhd_of_isEmpty» := P2M_GroundTheory_Heights__Heights_Model_spreadNbhd_of_isEmpty_9b72b381a6b7
