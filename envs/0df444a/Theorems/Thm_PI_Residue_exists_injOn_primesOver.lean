-- Prove2me | Theorems.Thm_PI_Residue_exists_injOn_primesOver
-- name    : PI.Residue.exists_injOn_primesOver
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:19:34.694137+00:00
-- url     : https://prove2.me/theorems/bfe48cfd-1987-43e8-afd8-14393c7af870
-- title:
--   Residue: exists inj On primes Over
-- statement:
--   The Residue construction uses the exists inj On primes Over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/UnderEqOfNotCoprime.lean#L25-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/UnderEqOfNotCoprime.lean#L25-L37

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
set_option linter.deprecated false

theorem PI.Residue.exists_injOn_primesOver (p : Ideal ℤ) [p.IsMaximal] (hp : p ≠ ⊥) :
    ∃ g : Ideal (𝓞 E) → Fin (Module.finrank ℚ E), Set.InjOn g (p.primesOver (𝓞 E)) := by sorry
