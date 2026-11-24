-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_IsBasisOn_bijective_self_4d7cdc831e38
-- name    : P2M_GroundTheory_Heights__Heights_Model_IsBasisOn_bijective_self_4d7cdc831e38
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:25:36.645145+00:00
-- url     : https://prove2.me/theorems/ad926cdb-d609-402d-bea8-ce8aca4c194f
-- title:
--   P2 M Ground Theory Heights  Heights Model Is Basis On bijective self 4d7cdc831e38: P2 M Ground Theory Heights  Heights Model Is Basis On bijective self 4d7cdc831e38
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Is Basis On bijective self 4d7cdc831e38 construction uses the P2 M Ground Theory Heights  Heights Model Is Basis On bijective self 4d7cdc831e38 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PClearDenominators.lean#L44-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PClearDenominators.lean#L44-L50

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
variable {X : Scheme.{0}} (M : X.Modules)
variable {M}

theorem P2M_GroundTheory_Heights__Heights_Model_IsBasisOn_bijective_self_4d7cdc831e38 {U : X.Opens} {n : ℕ} {s : Fin n → Γ(M, U)} (hs : IsBasisOn M U s) :
    Function.Bijective (fun r : Fin n → Γ(X, U) => ∑ i, r i • s i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«IsBasisOn».«bijective_self» := P2M_GroundTheory_Heights__Heights_Model_IsBasisOn_bijective_self_4d7cdc831e38
