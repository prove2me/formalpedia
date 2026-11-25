-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_isMultiHomog_X_zero_b47684ca621c
-- name    : P2M_GroundTheory_Heights__Heights_Model_isMultiHomog_X_zero_b47684ca621c
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:34:10.643322+00:00
-- url     : https://prove2.me/theorems/b51b27d7-5f91-4953-9f91-c6e7c63a5d3b
-- title:
--   P2 M Ground Theory Heights  Heights Model is Multi Homog X zero b47684ca621c: P2 M Ground Theory Heights  Heights Model is Multi Homog X zero b47684ca621c
-- statement:
--   The P2 M Ground Theory Heights  Heights Model is Multi Homog X zero b47684ca621c construction uses the P2 M Ground Theory Heights  Heights Model is Multi Homog X zero b47684ca621c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L584-L592
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L584-L592

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
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
open NumbersDVR ReciprocityTheory.ChartRestriction.G.Geo

theorem P2M_GroundTheory_Heights__Heights_Model_isMultiHomog_X_zero_b47684ca621c :
    IsMultiHomog (MvPolynomial.X ⟨(), 0⟩ : MRing (fun _ : Unit => Fin 2) ℚ) (fun _ => 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«isMultiHomog_X_zero» := P2M_GroundTheory_Heights__Heights_Model_isMultiHomog_X_zero_b47684ca621c
