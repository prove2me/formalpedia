-- Prove2me | Theorems.Thm_PI_PrimesDyadicRS_K_loop_sound
-- name    : PI.PrimesDyadicRS.K.loop_sound
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:37:00.404063+00:00
-- url     : https://prove2.me/theorems/32618ed5-a0cb-4167-b4da-df3fd9b1b0af
-- title:
--   K: loop sound
-- statement:
--   The K construction uses the loop sound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DyadicPrimeIntervals/SmallNaturalNumbersBound.lean#L81-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DyadicPrimeIntervals/SmallNaturalNumbersBound.lean#L81-L105

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_ThetaDiff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_SmallLoop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_Run1
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_Run2
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_Run3
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_Run4
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_SmallNaturalNumbersBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.PrimesDyadicRS PI.PrimesDyadicRS.K
open Real

theorem PI.PrimesDyadicRS.K.loop_sound {Q hT dT : ℕ} (hQ : Q = Nat.factorial 362) :
    ∀ k h d : ℕ, loop Q hT dT k h d = true → 2 ≤ h → h + k ≤ 131072 → d = D h →
      (hT = h + k ∧ dT = D hT) ∧ ∀ m, h ≤ m → m < h + k → 41 ≤ m → tstR m (D m) = true := by sorry
