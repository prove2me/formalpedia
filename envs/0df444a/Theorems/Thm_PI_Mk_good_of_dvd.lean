-- Prove2me | Theorems.Thm_PI_Mk_good_of_dvd
-- name    : PI.Mk.good_of_dvd
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:35:16.409295+00:00
-- url     : https://prove2.me/theorems/d3e1c3c4-f8fc-494a-a7d4-e98d1c96e5cc
-- title:
--   Mk: good of dvd
-- statement:
--   The Mk construction uses the good of dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinkowskiBound/CharpolyDvdOfPowEqOne.lean#L102-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinkowskiBound/CharpolyDvdOfPowEqOne.lean#L102-L129

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

theorem PI.Mk.good_of_dvd (ℓ : ℕ) (hℓ : ℓ.Prime) (a M : ℕ) (p : ℚ[X]) (hp : p.Monic)
    (hd : p ∣ (X ^ (ℓ ^ a) - 1 : ℚ[X]) ^ M) : Good ℓ p := by sorry
