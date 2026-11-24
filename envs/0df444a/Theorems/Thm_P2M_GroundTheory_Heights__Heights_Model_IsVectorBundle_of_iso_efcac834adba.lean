-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_IsVectorBundle_of_iso_efcac834adba
-- name    : P2M_GroundTheory_Heights__Heights_Model_IsVectorBundle_of_iso_efcac834adba
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:19:40.375697+00:00
-- url     : https://prove2.me/theorems/0affbba7-53eb-410e-9c15-859470cc502a
-- title:
--   P2 M Ground Theory Heights  Heights Model Is Vector Bundle of iso efcac834adba: P2 M Ground Theory Heights  Heights Model Is Vector Bundle of iso efcac834adba
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Is Vector Bundle of iso efcac834adba construction uses the P2 M Ground Theory Heights  Heights Model Is Vector Bundle of iso efcac834adba property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L434-L438
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L434-L438

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

theorem P2M_GroundTheory_Heights__Heights_Model_IsVectorBundle_of_iso_efcac834adba {M N : X.Modules} (e : M ≅ N) (hM : IsVectorBundle M) :
    IsVectorBundle N := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«IsVectorBundle».«of_iso» := P2M_GroundTheory_Heights__Heights_Model_IsVectorBundle_of_iso_efcac834adba
