-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_HeightOneSections_germ_coeff_unique_f4d9ebe0d3b7
-- name    : P2M_GroundTheory_Heights__Heights_Model_HeightOneSections_germ_coeff_unique_f4d9ebe0d3b7
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:30:31.496053+00:00
-- url     : https://prove2.me/theorems/683e0e80-c6b1-475f-b16c-50bb25191a35
-- title:
--   P2 M Ground Theory Heights  Heights Model Height One Sections germ coeff unique f4d9ebe0d3b7: P2 M Ground Theory Heights  Heights Model Height One Sections germ coeff unique f4d9ebe0d3b7
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Height One Sections germ coeff unique f4d9ebe0d3b7 construction uses the P2 M Ground Theory Heights  Heights Model Height One Sections germ coeff unique f4d9ebe0d3b7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PHeightOneSectionsLocal.lean#L71-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PHeightOneSectionsLocal.lean#L71-L86

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

theorem P2M_GroundTheory_Heights__Heights_Model_HeightOneSections_germ_coeff_unique_f4d9ebe0d3b7 (E : X.Modules) {V : X.Opens} {n : ℕ} {s : Fin n → Γ(E, V)}
    (hs : IsBasisOn E V s) (x : X) (hxV : x ∈ V) {W W' : X.Opens} (h : W ≤ V) (h' : W' ≤ V)
    (hx : x ∈ W) (hx' : x ∈ W') (r : Fin n → Γ(X, W)) (r' : Fin n → Γ(X, W'))
    (e : ∑ i, X.presheaf.germ W x hx (r i) • E.presheaf.germ V x hxV (s i) =
      ∑ i, X.presheaf.germ W' x hx' (r' i) • E.presheaf.germ V x hxV (s i)) (i : Fin n) :
    X.presheaf.germ W x hx (r i) = X.presheaf.germ W' x hx' (r' i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«HeightOneSections».«germ_coeff_unique» := P2M_GroundTheory_Heights__Heights_Model_HeightOneSections_germ_coeff_unique_f4d9ebe0d3b7
