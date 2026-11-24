-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_GlobalClassField_galRestrict_apply_eq_smul
-- name    : ReciprocityTheory.DiscreteGroups.GlobalClassField.galRestrict_apply_eq_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:19.197483+00:00
-- url     : https://prove2.me/theorems/aa323a1d-dd28-4a7c-8f36-0ede195084ec
-- title:
--   Global Class Field: gal Restrict apply eq smul
-- statement:
--   The Global Class Field construction uses the gal Restrict apply eq smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/GlobalClassField/IsFrobAtMulOfMemInertiaGroup.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/GlobalClassField/IsFrobAtMulOfMemInertiaGroup.lean#L22-L25

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

theorem ReciprocityTheory.DiscreteGroups.GlobalClassField.galRestrict_apply_eq_smul (τ : L ≃ₐ[K] L) (x : 𝓞 L) :
    galRestrict (𝓞 K) K L (𝓞 L) τ x = τ • x := by sorry
