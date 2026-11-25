-- Prove2me | Theorems.Thm_PI_Mk_padicValNat_pow_mul_factorial
-- name    : PI.Mk.padicValNat_pow_mul_factorial
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:35:18.678307+00:00
-- url     : https://prove2.me/theorems/386c2096-f8bd-596d-8eb5-d21deaa0dd96
-- title:
--   Mk: padic Val Nat pow mul factorial
-- statement:
--   The Mk construction uses the padic Val Nat pow mul factorial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinkowskiBound/Assemble.lean#L12-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinkowskiBound/Assemble.lean#L12-L23

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_Minkowski
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_PowerSumStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_Assemble
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Mk
open Finset

theorem PI.Mk.padicValNat_pow_mul_factorial (N ℓ : ℕ) (hℓ : ℓ.Prime) :
    padicValNat ℓ (ℓ ^ (N / (ℓ - 1)) * (N / (ℓ - 1)).factorial) = PI.minkowskiExp N ℓ := by sorry
