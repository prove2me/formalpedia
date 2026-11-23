-- Prove2me | Theorems.Thm_PI_Mk_good_mul
-- name    : PI.Mk.good_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:26:19.517822+00:00
-- url     : https://prove2.me/theorems/af4dd421-0ea3-4e97-916f-cd3c484e8599
-- title:
--   Mk: good mul
-- statement:
--   The Mk construction uses the good mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinkowskiBound/CharpolyDvdOfPowEqOne.lean#L33-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinkowskiBound/CharpolyDvdOfPowEqOne.lean#L33-L44

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

theorem PI.Mk.good_mul (ℓ : ℕ) (p q : ℚ[X]) (hp : Good ℓ p) (hq : Good ℓ q) : Good ℓ (p * q) := by sorry
