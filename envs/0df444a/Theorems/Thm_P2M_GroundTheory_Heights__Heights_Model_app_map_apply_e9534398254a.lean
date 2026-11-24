-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_app_map_apply_e9534398254a
-- name    : P2M_GroundTheory_Heights__Heights_Model_app_map_apply_e9534398254a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:22:47.485959+00:00
-- url     : https://prove2.me/theorems/a19cf10d-ecdc-4ad2-9d4d-57760cac520d
-- title:
--   P2 M Ground Theory Heights  Heights Model app map apply e9534398254a: P2 M Ground Theory Heights  Heights Model app map apply e9534398254a
-- statement:
--   The P2 M Ground Theory Heights  Heights Model app map apply e9534398254a construction uses the P2 M Ground Theory Heights  Heights Model app map apply e9534398254a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L415-L419
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L415-L419

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
universe u
variable {X Y : Scheme.{u}}

theorem P2M_GroundTheory_Heights__Heights_Model_app_map_apply_e9534398254a {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (i : V ≤ U) (x : Γ(M, U)) :
    (φ.app V).hom ((M.presheaf.map (homOfLE i).op).hom x) =
      (N.presheaf.map (homOfLE i).op).hom ((φ.app U).hom x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«app_map_apply» := P2M_GroundTheory_Heights__Heights_Model_app_map_apply_e9534398254a
