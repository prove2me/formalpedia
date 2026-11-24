-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_pullSectionOn_smul_bc982e9b6cbd
-- name    : P2M_GroundTheory_Heights__Heights_Model_pullSectionOn_smul_bc982e9b6cbd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:12.250183+00:00
-- url     : https://prove2.me/theorems/beb6c9e1-7020-4a11-a311-67ca8f05b3dd
-- title:
--   P2 M Ground Theory Heights  Heights Model pull Section On smul bc982e9b6cbd: P2 M Ground Theory Heights  Heights Model pull Section On smul bc982e9b6cbd
-- statement:
--   The P2 M Ground Theory Heights  Heights Model pull Section On smul bc982e9b6cbd construction uses the P2 M Ground Theory Heights  Heights Model pull Section On smul bc982e9b6cbd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PClearDenominators.lean#L58-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PClearDenominators.lean#L58-L60

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

theorem P2M_GroundTheory_Heights__Heights_Model_pullSectionOn_smul_bc982e9b6cbd (U : Z.Opens) (r : Γ(Z, U)) (m : Γ(M, U)) :
    pullSectionOn g M U (r • m) = g.app U r • pullSectionOn g M U m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«pullSectionOn_smul» := P2M_GroundTheory_Heights__Heights_Model_pullSectionOn_smul_bc982e9b6cbd
