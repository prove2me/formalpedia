-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_eq_zero_of_mem_BrKer_of_coprime
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.eq_zero_of_mem_BrKer_of_coprime
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:53:57.897156+00:00
-- url     : https://prove2.me/theorems/58744587-6427-5479-8ff6-86d7d71c92f7
-- title:
--   Local Class Field: eq zero of mem Br Ker of coprime
-- statement:
--   The Local Class Field construction uses the eq zero of mem Br Ker of coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/EqZeroOfMemBrKerOfCoprime.lean#L55-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/EqZeroOfMemBrKerOfCoprime.lean#L55-L60

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RestrictedMultiplicativeH1Subsingleton
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_EqZeroOfResEqZeroOfCoprime
import Definitions.Def_ReciprocityTheory_GroupCohomology_FiniteLevel
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_EqZeroOfMemBrKerOfCoprime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh Function
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
variable {p K L}

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.eq_zero_of_mem_BrKer_of_coprime (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) (x : Br p K)
    (hx : x ∈ BrKer h) (k : ℕ) (hk : k • x = 0) (hc : Nat.Coprime k (degLK p K L)) : x = 0 := by sorry
