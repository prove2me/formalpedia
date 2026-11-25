-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_pullSectionOn_top_f6a301beb699
-- name    : P2M_GroundTheory_Heights__Heights_Model_pullSectionOn_top_f6a301beb699
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:29:36.181819+00:00
-- url     : https://prove2.me/theorems/b244d93d-7d5d-4636-8bf6-1565d6d7a4bc
-- title:
--   P2 M Ground Theory Heights  Heights Model pull Section On top f6a301beb699: P2 M Ground Theory Heights  Heights Model pull Section On top f6a301beb699
-- statement:
--   The P2 M Ground Theory Heights  Heights Model pull Section On top f6a301beb699 construction uses the P2 M Ground Theory Heights  Heights Model pull Section On top f6a301beb699 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PullbackBasis.lean#L17-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PullbackBasis.lean#L17-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PullbackBasis
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
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
universe u

theorem P2M_GroundTheory_Heights__Heights_Model_pullSectionOn_top_f6a301beb699 {T Z : Scheme.{u}} (g : T ⟶ Z) (M : Z.Modules) :
    pullSectionOn g M ⊤ = pullSection g M := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«pullSectionOn_top» := P2M_GroundTheory_Heights__Heights_Model_pullSectionOn_top_f6a301beb699
