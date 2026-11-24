-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_GlobalClassField_isFrobAt_iff_forall
-- name    : ReciprocityTheory.DiscreteGroups.GlobalClassField.isFrobAt_iff_forall
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:58:30.510868+00:00
-- url     : https://prove2.me/theorems/c768b73a-cc7b-4470-958f-9f0c4559d557
-- title:
--   Global Class Field: is Frob At iff forall
-- statement:
--   The Global Class Field construction uses the is Frob At iff forall property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/GlobalClassField/IsFrobAtMulOfMemInertiaGroup.lean#L34-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/GlobalClassField/IsFrobAtMulOfMemInertiaGroup.lean#L34-L37

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

theorem ReciprocityTheory.DiscreteGroups.GlobalClassField.isFrobAt_iff_forall (τ : L ≃ₐ[K] L) (Q : Ideal (𝓞 L)) :
    IsFrobAt K L τ Q ↔ ∀ x : 𝓞 L, τ • x - x ^ Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) ∈ Q := by sorry
