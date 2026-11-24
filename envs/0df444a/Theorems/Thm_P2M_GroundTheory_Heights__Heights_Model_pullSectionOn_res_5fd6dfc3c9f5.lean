-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_pullSectionOn_res_5fd6dfc3c9f5
-- name    : P2M_GroundTheory_Heights__Heights_Model_pullSectionOn_res_5fd6dfc3c9f5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:00.03288+00:00
-- url     : https://prove2.me/theorems/24d34fce-79b3-4f95-bb8d-8e01fd9d55bd
-- title:
--   P2 M Ground Theory Heights  Heights Model pull Section On res 5fd6dfc3c9f5: P2 M Ground Theory Heights  Heights Model pull Section On res 5fd6dfc3c9f5
-- statement:
--   The P2 M Ground Theory Heights  Heights Model pull Section On res 5fd6dfc3c9f5 construction uses the P2 M Ground Theory Heights  Heights Model pull Section On res 5fd6dfc3c9f5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PClearDenominators.lean#L62-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PClearDenominators.lean#L62-L70

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PullbackBasis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_RatLocalAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PVectorBundleRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PClearDenominators
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
variable {T Z : Scheme.{0}} (g : T ⟶ Z) (M : Z.Modules)

theorem P2M_GroundTheory_Heights__Heights_Model_pullSectionOn_res_5fd6dfc3c9f5 {U V : Z.Opens} (h : V ≤ U) (i : g ⁻¹ᵁ V ⟶ g ⁻¹ᵁ U) (m : Γ(M, U)) :
    pullSectionOn g M V ((M.presheaf.map (homOfLE h).op).hom m) =
      (((Scheme.Modules.pullback g).obj M).presheaf.map i.op).hom (pullSectionOn g M U m) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«pullSectionOn_res» := P2M_GroundTheory_Heights__Heights_Model_pullSectionOn_res_5fd6dfc3c9f5
