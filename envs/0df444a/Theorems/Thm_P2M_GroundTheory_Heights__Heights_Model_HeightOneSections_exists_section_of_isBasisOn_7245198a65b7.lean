-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_HeightOneSections_exists_section_of_isBasisOn_7245198a65b7
-- name    : P2M_GroundTheory_Heights__Heights_Model_HeightOneSections_exists_section_of_isBasisOn_7245198a65b7
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:30:25.9358+00:00
-- url     : https://prove2.me/theorems/999d6133-fb8f-4035-9cb6-cb8041f9a23e
-- title:
--   P2 M Ground Theory Heights  Heights Model Height One Sections exists section of is Basis On 7245198a65b7: P2 M Ground Theory Heights  Heights Model Height One Sections exists section of is Basis On 72
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Height One Sections exists section of is Basis On 7245198a65b7 construction uses the P2 M Ground Theory Heights  Heights Model Height One Sections exists section of is Basis On 7245198a65b7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PHeightOneSectionsLocal.lean#L88-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PHeightOneSectionsLocal.lean#L88-L158

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

theorem P2M_GroundTheory_Heights__Heights_Model_HeightOneSections_exists_section_of_isBasisOn_7245198a65b7 (hHOI : HeightOneIntersection.Statement)
    [IsLocallyNoetherian X] (hN : IsNormalScheme X) (E : X.Modules) {V : X.Opens}
    (hV : IsAffineOpen V) (hη : genericPoint X ∈ V) {n : ℕ} {s : Fin n → Γ(E, V)}
    (hs : IsBasisOn E V s) (v : E.presheaf.stalk (genericPoint X))
    (hv : ∀ y : X, y ∈ V → ringKrullDim (X.presheaf.stalk y) = 1 → v ∈ genericImage E y) :
    ∃ σ : Γ(E, V), E.presheaf.germ V (genericPoint X) hη σ = v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«HeightOneSections».«exists_section_of_isBasisOn» := P2M_GroundTheory_Heights__Heights_Model_HeightOneSections_exists_section_of_isBasisOn_7245198a65b7
