-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_SpreadsOn_toNbhd_7b57d76b6882
-- name    : P2M_GroundTheory_Heights__Heights_Model_SpreadsOn_toNbhd_7b57d76b6882
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:29:19.923076+00:00
-- url     : https://prove2.me/theorems/7ec3efc6-440e-4da2-845e-ee06924049f9
-- title:
--   P2 M Ground Theory Heights  Heights Model Spreads On to Nbhd 7b57d76b6882: P2 M Ground Theory Heights  Heights Model Spreads On to Nbhd 7b57d76b6882
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Spreads On to Nbhd 7b57d76b6882 construction uses the P2 M Ground Theory Heights  Heights Model Spreads On to Nbhd 7b57d76b6882 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PSpreadBundleNbhd.lean#L14-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PSpreadBundleNbhd.lean#L14-L33

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

theorem P2M_GroundTheory_Heights__Heights_Model_SpreadsOn_toNbhd_7b57d76b6882 (f : X ⟶ SpecZ) (R : Type) [CommRing R] {E : (baseChange f R).Modules}
    {W : X.Opens} (hE : SpreadsOn f R E W) (htop : ⊤ ≤ baseChangeMap f R ⁻¹ᵁ W) :
    ∃ (hW : Set.range (baseChangeMap f R) ⊆ Set.range W.ι) (E' : (W : Scheme.{0}).Modules),
      IsVectorBundle E' ∧ Nonempty ((Scheme.Modules.pullback (toOpen f R W hW)).obj E' ≅ E) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«SpreadsOn».«toNbhd» := P2M_GroundTheory_Heights__Heights_Model_SpreadsOn_toNbhd_7b57d76b6882
