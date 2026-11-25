-- Prove2me | Theorems.Thm_PI_Mk_pow_minkowskiExp_dvd
-- name    : PI.Mk.pow_minkowskiExp_dvd
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:35:29.928381+00:00
-- url     : https://prove2.me/theorems/faf22d89-8d16-43e8-88a1-f525f218398f
-- title:
--   Mk: pow minkowski Exp dvd
-- statement:
--   The Mk construction uses the pow minkowski Exp dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinkowskiBound/Assemble.lean#L32-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinkowskiBound/Assemble.lean#L32-L39

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

theorem PI.Mk.pow_minkowskiExp_dvd (N ℓ : ℕ) (hℓ : ℓ.Prime) :
    ℓ ^ PI.minkowskiExp N ℓ ∣ PI.minkowskiM N := by sorry
