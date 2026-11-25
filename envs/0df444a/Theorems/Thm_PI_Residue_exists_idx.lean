-- Prove2me | Theorems.Thm_PI_Residue_exists_idx
-- name    : PI.Residue.exists_idx
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:19:25.941722+00:00
-- url     : https://prove2.me/theorems/d299bec3-cca4-5903-9b94-750d1ac4931a
-- title:
--   Residue: exists idx
-- statement:
--   The Residue construction uses the exists idx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/UnderEqOfNotCoprime.lean#L65-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/UnderEqOfNotCoprime.lean#L65-L87

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
variable (E)

theorem PI.Residue.exists_idx : ∃ idx : Ideal (𝓞 E) → Fin (Module.finrank ℚ E),
    ∀ P ∈ primeSet E, ∀ Q ∈ primeSet E, idx P = idx Q →
      ¬ Nat.Coprime (absNorm P) (absNorm Q) → P = Q := by sorry
