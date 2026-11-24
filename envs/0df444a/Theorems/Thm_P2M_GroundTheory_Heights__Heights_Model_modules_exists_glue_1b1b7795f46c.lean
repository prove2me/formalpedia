-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_modules_exists_glue_1b1b7795f46c
-- name    : P2M_GroundTheory_Heights__Heights_Model_modules_exists_glue_1b1b7795f46c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:45.889815+00:00
-- url     : https://prove2.me/theorems/939a6790-bf7f-4387-9869-12038881691d
-- title:
--   P2 M Ground Theory Heights  Heights Model modules exists glue 1b1b7795f46c: P2 M Ground Theory Heights  Heights Model modules exists glue 1b1b7795f46c
-- statement:
--   The P2 M Ground Theory Heights  Heights Model modules exists glue 1b1b7795f46c construction uses the P2 M Ground Theory Heights  Heights Model modules exists glue 1b1b7795f46c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PClearDenominators.lean#L32-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PClearDenominators.lean#L32-L40

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

theorem P2M_GroundTheory_Heights__Heights_Model_modules_exists_glue_1b1b7795f46c {V : X.Opens} {ι : Type} (W : ι → X.Opens) (i : ∀ a, W a ≤ V)
    (hcov : ∀ x ∈ V, ∃ a, x ∈ W a) (sf : ∀ a, Γ(M, W a))
    (hsf : ∀ a b, (M.presheaf.map (homOfLE (inf_le_left : W a ⊓ W b ≤ W a)).op).hom (sf a) =
      (M.presheaf.map (homOfLE (inf_le_right : W a ⊓ W b ≤ W b)).op).hom (sf b)) :
    ∃ s : Γ(M, V), ∀ a, (M.presheaf.map (homOfLE (i a)).op).hom s = sf a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«modules_exists_glue» := P2M_GroundTheory_Heights__Heights_Model_modules_exists_glue_1b1b7795f46c
