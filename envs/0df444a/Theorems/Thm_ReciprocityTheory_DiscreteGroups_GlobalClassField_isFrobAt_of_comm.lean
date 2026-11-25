-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_GlobalClassField_isFrobAt_of_comm
-- name    : ReciprocityTheory.DiscreteGroups.GlobalClassField.isFrobAt_of_comm
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:51:24.524793+00:00
-- url     : https://prove2.me/theorems/cb182233-de96-5ae6-8219-f694ac26767b
-- title:
--   Global Class Field: is Frob At of comm
-- statement:
--   The Global Class Field construction uses the is Frob At of comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/GlobalClassField/IsFrobAtMulOfMemInertiaGroup.lean#L81-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/GlobalClassField/IsFrobAtMulOfMemInertiaGroup.lean#L81-L85

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
variable (v : HeightOneSpectrum (𝓞 K)) (Q Q' : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver v.asIdeal]
variable [IsGalois K L]

theorem ReciprocityTheory.DiscreteGroups.GlobalClassField.isFrobAt_of_comm (hc : ∀ a b : L ≃ₐ[K] L, a * b = b * a) [Q'.IsPrime]
    [Q'.LiesOver v.asIdeal] (τ : L ≃ₐ[K] L) (h : IsFrobAt K L τ Q) : IsFrobAt K L τ Q' := by sorry
