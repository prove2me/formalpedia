-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_pullbackHomAlong_comp_612936c62fe2
-- name    : P2M_GroundTheory_Heights__Heights_Model_pullbackHomAlong_comp_612936c62fe2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:28:52.427748+00:00
-- url     : https://prove2.me/theorems/5e6198c3-0958-4448-bc72-6b95c188da8d
-- title:
--   P2 M Ground Theory Heights  Heights Model pullback Hom Along comp 612936c62fe2: P2 M Ground Theory Heights  Heights Model pullback Hom Along comp 612936c62fe2
-- statement:
--   The P2 M Ground Theory Heights  Heights Model pullback Hom Along comp 612936c62fe2 construction uses the P2 M Ground Theory Heights  Heights Model pullback Hom Along comp 612936c62fe2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/StatementsSpreadHom.lean#L26-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/StatementsSpreadHom.lean#L26-L30

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

theorem P2M_GroundTheory_Heights__Heights_Model_pullbackHomAlong_comp_612936c62fe2 (e : g ≫ h = k) {F G H : Z.Modules}
    (ψ : (Scheme.Modules.pullback h).obj F ⟶ (Scheme.Modules.pullback h).obj G)
    (ψ' : (Scheme.Modules.pullback h).obj G ⟶ (Scheme.Modules.pullback h).obj H) :
    pullbackHomAlong e (ψ ≫ ψ') = pullbackHomAlong e ψ ≫ pullbackHomAlong e ψ' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«pullbackHomAlong_comp» := P2M_GroundTheory_Heights__Heights_Model_pullbackHomAlong_comp_612936c62fe2
