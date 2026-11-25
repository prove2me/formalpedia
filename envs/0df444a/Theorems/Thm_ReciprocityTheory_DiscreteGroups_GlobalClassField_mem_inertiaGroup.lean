-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_GlobalClassField_mem_inertiaGroup
-- name    : ReciprocityTheory.DiscreteGroups.GlobalClassField.mem_inertiaGroup
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:51:37.52689+00:00
-- url     : https://prove2.me/theorems/78dcfe94-afb8-55d4-a6a7-bacb1cd4c7cd
-- title:
--   Global Class Field: mem inertia Group
-- statement:
--   The Global Class Field construction uses the mem inertia Group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/GlobalClassField/IsFrobAtMulOfMemInertiaGroup.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/GlobalClassField/IsFrobAtMulOfMemInertiaGroup.lean#L18-L20

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_GlobalClassField_SUnitGalois_GalSmulAsIdeal
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_GlobalClassField_IsFrobAtMulOfMemInertiaGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1
open scoped Pointwise
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.GlobalClassField
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {K L}

theorem ReciprocityTheory.DiscreteGroups.GlobalClassField.mem_inertiaGroup {Q : Ideal (𝓞 L)} {τ : L ≃ₐ[K] L} :
    τ ∈ inertiaGroup K L Q ↔ ∀ x : 𝓞 L, galRestrict (𝓞 K) K L (𝓞 L) τ x - x ∈ Q := by sorry
