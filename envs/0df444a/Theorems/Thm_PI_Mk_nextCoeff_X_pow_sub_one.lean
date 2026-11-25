-- Prove2me | Theorems.Thm_PI_Mk_nextCoeff_X_pow_sub_one
-- name    : PI.Mk.nextCoeff_X_pow_sub_one
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:35:21.687061+00:00
-- url     : https://prove2.me/theorems/25b2e845-1e17-4080-a787-13722b703bb9
-- title:
--   Mk: next Coeff X pow sub one
-- statement:
--   The Mk construction uses the next Coeff X pow sub one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinkowskiBound/CharpolyDvdOfPowEqOne.lean#L46-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinkowskiBound/CharpolyDvdOfPowEqOne.lean#L46-L55

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_PowerSumStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiBound_CharpolyDvdOfPowEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Mk
open Polynomial Matrix

theorem PI.Mk.nextCoeff_X_pow_sub_one (n : ℕ) (hn : 0 < n) :
    (X ^ n - 1 : ℚ[X]).nextCoeff = if n = 1 then -1 else 0 := by sorry
