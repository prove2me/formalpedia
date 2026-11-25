-- Prove2me | Theorems.Thm_PI_Residue_under_eq_of_not_coprime
-- name    : PI.Residue.under_eq_of_not_coprime
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:19:50.10355+00:00
-- url     : https://prove2.me/theorems/6bc80919-c2c9-4ae3-9c93-021a4388080c
-- title:
--   Residue: under eq of not coprime
-- statement:
--   The Residue construction uses the under eq of not coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/UnderEqOfNotCoprime.lean#L41-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/UnderEqOfNotCoprime.lean#L41-L61

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_FactorizationMultisetProd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnderEqOfNotCoprime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Residue
open NumberField Ideal UniqueFactorizationMonoid
open scoped ENNReal
variable (E : Type*) [Field E] [NumberField E]
variable {E}
variable (E)
variable {E}

theorem PI.Residue.under_eq_of_not_coprime {P Q : Ideal (𝓞 E)} (hP : P ∈ primeSet E) (hQ : Q ∈ primeSet E)
    (hcop : ¬ Nat.Coprime (absNorm P) (absNorm Q)) : P.under ℤ = Q.under ℤ := by sorry
