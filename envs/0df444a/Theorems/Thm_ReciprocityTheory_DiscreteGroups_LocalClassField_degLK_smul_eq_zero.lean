-- Prove2me | Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_degLK_smul_eq_zero
-- name    : ReciprocityTheory.DiscreteGroups.LocalClassField.degLK_smul_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:24.4798+00:00
-- url     : https://prove2.me/theorems/c39a0e81-25d3-4e7a-91dd-f5042bd662eb
-- title:
--   Local Class Field: deg LK smul eq zero
-- statement:
--   The Local Class Field construction uses the deg LK smul eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/EqZeroOfMemBrKerOfCoprime.lean#L47-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/EqZeroOfMemBrKerOfCoprime.lean#L47-L53

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

theorem ReciprocityTheory.DiscreteGroups.LocalClassField.degLK_smul_eq_zero (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) (x : Br p K) (hx : x ∈ BrKer h) :
    degLK p K L • x = 0 := by sorry
