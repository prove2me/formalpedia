-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_HeightOneSections_comb_res_b8d8455008cb
-- name    : P2M_GroundTheory_Heights__Heights_Model_HeightOneSections_comb_res_b8d8455008cb
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:30:26.197847+00:00
-- url     : https://prove2.me/theorems/00638096-f822-4b97-ae71-3536a3614028
-- title:
--   P2 M Ground Theory Heights  Heights Model Height One Sections comb res b8d8455008cb: P2 M Ground Theory Heights  Heights Model Height One Sections comb res b8d8455008cb
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Height One Sections comb res b8d8455008cb construction uses the P2 M Ground Theory Heights  Heights Model Height One Sections comb res b8d8455008cb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PHeightOneSectionsLocal.lean#L57-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PHeightOneSectionsLocal.lean#L57-L67

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PBundlesAgree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PHeightOneSectionsLocal
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
open GroundTheory.Heights₂.Heights.Model.HeightOneSections
variable {X : Scheme.{0}} [IsIntegral X]
omit [IsIntegral X]

theorem P2M_GroundTheory_Heights__Heights_Model_HeightOneSections_comb_res_b8d8455008cb (E : X.Modules) {V : X.Opens} {n : ℕ} (s : Fin n → Γ(E, V)) (W W' : X.Opens)
    (h : W ≤ V) (h' : W' ≤ W) (r : Fin n → Γ(X, W)) :
    E.presheaf.map (homOfLE h').op (comb E s W h r) =
      comb E s W' (h'.trans h) (fun i => X.presheaf.map (homOfLE h').op (r i)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«HeightOneSections».«comb_res» := P2M_GroundTheory_Heights__Heights_Model_HeightOneSections_comb_res_b8d8455008cb
