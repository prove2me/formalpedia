-- Prove2me | Theorems.Thm_PI_FiltrationLength_length_quot_le_of_ker_le
-- name    : PI.FiltrationLength.length_quot_le_of_ker_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:45:26.566452+00:00
-- url     : https://prove2.me/theorems/2c94a7f5-6d9f-4a68-93c5-cf3926055727
-- title:
--   Filtration Length: length quot le of ker le
-- statement:
--   The Filtration Length construction uses the length quot le of ker le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiltrationLength/LengthQuotLeOfKerLe.lean#L58-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiltrationLength/LengthQuotLeOfKerLe.lean#L58-L71

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FiltLen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiltrationLength_LengthQuotLeOfKerLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.FiltrationLength
open Submodule
variable {R W : Type} [CommRing R] [AddCommGroup W] [Module R W]

theorem PI.FiltrationLength.length_quot_le_of_ker_le {X Y : Type} [AddCommGroup X] [Module R X] [AddCommGroup Y]
    [Module R Y] (g : X →ₗ[R] Y) (K : Submodule R X) (hK : LinearMap.ker g ≤ K) :
    Module.length R (X ⧸ K) ≤ Module.length R Y := by sorry
