-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_HeightOneSections_germ_comb_8d6e321d74e3
-- name    : P2M_GroundTheory_Heights__Heights_Model_HeightOneSections_germ_comb_8d6e321d74e3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:26:37.935629+00:00
-- url     : https://prove2.me/theorems/47f87eff-e7a6-48cd-ac5a-98c970c5b7bd
-- title:
--   P2 M Ground Theory Heights  Heights Model Height One Sections germ comb 8d6e321d74e3: P2 M Ground Theory Heights  Heights Model Height One Sections germ comb 8d6e321d74e3
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Height One Sections germ comb 8d6e321d74e3 construction uses the P2 M Ground Theory Heights  Heights Model Height One Sections germ comb 8d6e321d74e3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PHeightOneSectionsLocal.lean#L45-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PHeightOneSectionsLocal.lean#L45-L53

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

theorem P2M_GroundTheory_Heights__Heights_Model_HeightOneSections_germ_comb_8d6e321d74e3 (E : X.Modules) {V : X.Opens} {n : ℕ} (s : Fin n → Γ(E, V)) (W : X.Opens)
    (h : W ≤ V) (r : Fin n → Γ(X, W)) (x : X) (hx : x ∈ W) :
    E.presheaf.germ W x hx (comb E s W h r) =
      ∑ i, X.presheaf.germ W x hx (r i) • E.presheaf.germ V x (h hx) (s i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«HeightOneSections».«germ_comb» := P2M_GroundTheory_Heights__Heights_Model_HeightOneSections_germ_comb_8d6e321d74e3
