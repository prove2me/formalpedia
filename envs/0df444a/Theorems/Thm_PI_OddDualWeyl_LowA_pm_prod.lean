-- Prove2me | Theorems.Thm_PI_OddDualWeyl_LowA_pm_prod
-- name    : PI.OddDualWeyl.LowA.pm_prod
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:13:52.722051+00:00
-- url     : https://prove2.me/theorems/00ca8991-90e4-41bf-b200-aaf391d9db3c
-- title:
--   Low A: pm prod
-- statement:
--   The Low A construction uses the pm prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightDualOf.lean#L137-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OddDualWeylJacobian/HighestWeightDualOf.lean#L137-L153

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_MnrUpdateEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_HighestWeightDualOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl PI.OddDualWeyl.LowA
variable {R : Type*} [CommRing R]

theorem PI.OddDualWeyl.LowA.pm_prod {ι : Type*} (s : Finset ι) (u : ι → R) (e : ι → ℕ) (hu : ∀ i, u i = 1 ∨ u i = -1) :
    ∏ i ∈ s, u i ^ e i = 1 ∨ ∏ i ∈ s, u i ^ e i = -1 := by sorry
