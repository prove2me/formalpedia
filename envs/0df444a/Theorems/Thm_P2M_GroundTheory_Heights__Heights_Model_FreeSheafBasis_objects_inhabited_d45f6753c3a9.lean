-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_FreeSheafBasis_objects_inhabited_d45f6753c3a9
-- name    : P2M_GroundTheory_Heights__Heights_Model_FreeSheafBasis_objects_inhabited_d45f6753c3a9
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:33:36.481129+00:00
-- url     : https://prove2.me/theorems/481f15d1-7b7b-5e2a-8b2b-7e64b29fb61d
-- title:
--   P2 M Ground Theory Heights  Heights Model Free Sheaf Basis objects inhabited d45f6753c3a9: P2 M Ground Theory Heights  Heights Model Free Sheaf Basis objects inhabited d45f6753c3a9
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Free Sheaf Basis objects inhabited d45f6753c3a9 construction uses the P2 M Ground Theory Heights  Heights Model Free Sheaf Basis objects inhabited d45f6753c3a9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/StatementsFreeSheafBasis.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/StatementsFreeSheafBasis.lean#L23-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsFreeSheafBasis
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
universe u

theorem P2M_GroundTheory_Heights__Heights_Model_FreeSheafBasis_objects_inhabited_d45f6753c3a9 :
    Nonempty ((freeModule SpecZ 2 : SpecZ.Modules) ≅ freeModule SpecZ 2) ∧
      Nonempty (Fin 2 → Γ(freeModule SpecZ 2, ⊤)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«FreeSheafBasis».«objects_inhabited» := P2M_GroundTheory_Heights__Heights_Model_FreeSheafBasis_objects_inhabited_d45f6753c3a9
