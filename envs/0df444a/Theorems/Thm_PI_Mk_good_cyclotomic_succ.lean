-- Prove2me | Theorems.Thm_PI_Mk_good_cyclotomic_succ
-- name    : PI.Mk.good_cyclotomic_succ
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:35:17.677938+00:00
-- url     : https://prove2.me/theorems/6ab940c6-7ea7-4785-b9d6-81474c315ef5
-- title:
--   Mk: good cyclotomic succ
-- statement:
--   The Mk construction uses the good cyclotomic succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinkowskiBound/CharpolyDvdOfPowEqOne.lean#L63-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinkowskiBound/CharpolyDvdOfPowEqOne.lean#L63-L95

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

theorem PI.Mk.good_cyclotomic_succ (ℓ : ℕ) (hℓ : ℓ.Prime) (j : ℕ) :
    Good ℓ (cyclotomic (ℓ ^ (j + 1)) ℚ) := by sorry
