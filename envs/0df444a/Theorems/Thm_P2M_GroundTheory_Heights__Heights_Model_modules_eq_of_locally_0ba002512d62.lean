-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_modules_eq_of_locally_0ba002512d62
-- name    : P2M_GroundTheory_Heights__Heights_Model_modules_eq_of_locally_0ba002512d62
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:55.678118+00:00
-- url     : https://prove2.me/theorems/512d64d3-d4dc-48e1-a628-c720351a0ebe
-- title:
--   P2 M Ground Theory Heights  Heights Model modules eq of locally 0ba002512d62: P2 M Ground Theory Heights  Heights Model modules eq of locally 0ba002512d62
-- statement:
--   The P2 M Ground Theory Heights  Heights Model modules eq of locally 0ba002512d62 construction uses the P2 M Ground Theory Heights  Heights Model modules eq of locally 0ba002512d62 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PClearDenominators.lean#L22-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PClearDenominators.lean#L22-L30

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

theorem P2M_GroundTheory_Heights__Heights_Model_modules_eq_of_locally_0ba002512d62 {V : X.Opens} (a b : Γ(M, V))
    (h : ∀ x ∈ V, ∃ (W : X.Opens) (i : W ≤ V), x ∈ W ∧
      (M.presheaf.map (homOfLE i).op).hom a = (M.presheaf.map (homOfLE i).op).hom b) : a = b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«modules_eq_of_locally» := P2M_GroundTheory_Heights__Heights_Model_modules_eq_of_locally_0ba002512d62
