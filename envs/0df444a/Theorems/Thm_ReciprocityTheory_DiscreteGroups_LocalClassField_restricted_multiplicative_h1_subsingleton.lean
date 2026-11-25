-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_restricted_multiplicative_h1_subsingleton
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.restricted_multiplicative_h1_subsingleton
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:46:30.204862+00:00
-- url     : https://prove2.me/theorems/efbba4d9-592e-4007-b938-6ee9ce46e00c
-- title:
--   Local Class Field: restricted multiplicative h1 subsingleton
-- statement:
--   The Local Class Field construction uses the restricted multiplicative h1 subsingleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/RestrictedMultiplicativeH1Subsingleton.lean#L154-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/RestrictedMultiplicativeH1Subsingleton.lean#L154-L165

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Duality
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
import Definitions.Def_ReciprocityTheory_GroupCohomology_FiveTerm
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_KbarRepContAction
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RestrictedMultiplicativeH1Subsingleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1
open ReciprocityTheory.Coh ReciprocityTheory.Coh.InflationRestrictionInvariants
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.restricted_multiplicative_h1_subsingleton (H : Subgroup (GK p K)) :
    Subsingleton (((kbarT p K).resSub H).H 1) := by sorry
