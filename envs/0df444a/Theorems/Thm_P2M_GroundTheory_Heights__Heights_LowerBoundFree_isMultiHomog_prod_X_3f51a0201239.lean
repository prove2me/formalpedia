-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_isMultiHomog_prod_X_3f51a0201239
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_isMultiHomog_prod_X_3f51a0201239
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:13:06.02247+00:00
-- url     : https://prove2.me/theorems/a80ce3de-69c8-523d-bb1d-a0861772b61f
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free is Multi Homog prod X 3f51a0201239: P2 M Ground Theory Heights  Heights Lower Bound Free is Multi Homog prod X 3f51a0201239
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free is Multi Homog prod X 3f51a0201239 construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free is Multi Homog prod X 3f51a0201239 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/Values.lean#L76-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/Values.lean#L76-L93

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_IsFrameOverLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Values
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped Matrix
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {Ω : Type} [Field Ω]

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_isMultiHomog_prod_X_3f51a0201239 (c : (k : K) → ι k) :
    IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRing ι)) (fun _ => 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«isMultiHomog_prod_X» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_isMultiHomog_prod_X_3f51a0201239
