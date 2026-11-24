-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_pullbackIsoAlong_hom_ed4907f849de
-- name    : P2M_GroundTheory_Heights__Heights_Model_pullbackIsoAlong_hom_ed4907f849de
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:28:53.102846+00:00
-- url     : https://prove2.me/theorems/285ca040-11d8-40f3-b87a-58beb8881c7a
-- title:
--   P2 M Ground Theory Heights  Heights Model pullback Iso Along hom ed4907f849de: P2 M Ground Theory Heights  Heights Model pullback Iso Along hom ed4907f849de
-- statement:
--   The P2 M Ground Theory Heights  Heights Model pullback Iso Along hom ed4907f849de construction uses the P2 M Ground Theory Heights  Heights Model pullback Iso Along hom ed4907f849de property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/StatementsSpreadHom.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/StatementsSpreadHom.lean#L21-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadHom
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
open CategoryTheory AlgebraicGeometry
noncomputable section
variable {T Y Z : Scheme.{0}} {g : T ⟶ Y} {h : Y ⟶ Z} {k : T ⟶ Z}

theorem P2M_GroundTheory_Heights__Heights_Model_pullbackIsoAlong_hom_ed4907f849de (e : g ≫ h = k) {F G : Z.Modules}
    (ψ : (Scheme.Modules.pullback h).obj F ≅ (Scheme.Modules.pullback h).obj G) :
    (pullbackIsoAlong e ψ).hom = pullbackHomAlong e ψ.hom := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«pullbackIsoAlong_hom» := P2M_GroundTheory_Heights__Heights_Model_pullbackIsoAlong_hom_ed4907f849de
