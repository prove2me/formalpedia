-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_multiplicative_inflation_h2_injective
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.multiplicative_inflation_h2_injective
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:56:03.975922+00:00
-- url     : https://prove2.me/theorems/337b93ca-0231-4352-8ff9-6d89c4a35364
-- title:
--   Local Class Field: multiplicative inflation h2 injective
-- statement:
--   The Local Class Field construction uses the multiplicative inflation h2 injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/RestrictedMultiplicativeH1Subsingleton.lean#L184-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/RestrictedMultiplicativeH1Subsingleton.lean#L184-L195

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.multiplicative_inflation_h2_injective (N : Subgroup (GK p K)) [N.Normal] (hN : IsClosed (N : Set (GK p K)))
    (Q : TRep ℤ (GK p K ⧸ N)) (P : Pair Q (kbarT p K)) (hP : IsInvRep (kbarT p K) N Q P) :
    Function.Injective (P.hom.H 2) := by sorry
