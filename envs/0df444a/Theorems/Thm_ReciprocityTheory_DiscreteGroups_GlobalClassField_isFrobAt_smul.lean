-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_GlobalClassField_isFrobAt_smul
-- name    : ReciprocityTheory.DiscreteGroups.GlobalClassField.isFrobAt_smul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:51:23.557686+00:00
-- url     : https://prove2.me/theorems/614fb256-51c1-5c59-b4d0-2a7bb8a87dd2
-- title:
--   Global Class Field: is Frob At smul
-- statement:
--   The Global Class Field construction uses the is Frob At smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/GlobalClassField/IsFrobAtMulOfMemInertiaGroup.lean#L46-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/GlobalClassField/IsFrobAtMulOfMemInertiaGroup.lean#L46-L51

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

theorem ReciprocityTheory.DiscreteGroups.GlobalClassField.isFrobAt_smul (σ τ : L ≃ₐ[K] L) (Q : Ideal (𝓞 L)) (h : IsFrobAt K L τ Q) :
    IsFrobAt K L (σ * τ * σ⁻¹) (σ • Q) := by sorry
