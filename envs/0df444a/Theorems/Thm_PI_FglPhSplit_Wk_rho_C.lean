-- Prove2me | Theorems.Thm_PI_FglPhSplit_Wk_rho_C
-- name    : PI.FglPhSplit.Wk.rho_C
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:29:51.337809+00:00
-- url     : https://prove2.me/theorems/38363219-73a1-4617-b490-4d4a9018a63f
-- title:
--   Wk: rho C
-- statement:
--   The Wk construction uses the rho C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupSplitting/ExpCongruenceExtendsToSum.lean#L106-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupSplitting/ExpCongruenceExtendsToSum.lean#L106-L112

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_AddPreservesExpCongruence
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_OrthogonalSplitPolarizationVanishes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_ExpCongruenceExtendsToSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FglPhSplit PI.FglPhSplit.Wk
open PI.FglPhSplit
variable {K : Type} [Field K]
variable {ι ι' : Type} [Fintype ι]

theorem PI.FglPhSplit.Wk.rho_C (c : K) :
    rho (ι' := ι') (MvPowerSeries.C c : MvPowerSeries (ι ⊕ ι) K) = MvPowerSeries.C c := by sorry
