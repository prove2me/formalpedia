-- Prove2me | Theorems.Thm_PI_FglPhSplit_Wk_rho_be
-- name    : PI.FglPhSplit.Wk.rho_be
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:29:54.009116+00:00
-- url     : https://prove2.me/theorems/fb6ec300-8ff1-40b3-9660-adb7522e2d2c
-- title:
--   Wk: rho be
-- statement:
--   The Wk construction uses the rho be property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupSplitting/ExpCongruenceExtendsToSum.lean#L139-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupSplitting/ExpCongruenceExtendsToSum.lean#L139-L144

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
variable (g : Dat K) (hex0 : PowerSeries.constantCoeff g.ex = 0)
  (hl0 : PowerSeries.constantCoeff g.l = 0)
include hex0 hl0

theorem PI.FglPhSplit.Wk.rho_be {x y : MvPowerSeries (ι ⊕ ι) K} (hx : MvPowerSeries.constantCoeff x = 0)
    (hy : MvPowerSeries.constantCoeff y = 0) :
    rho (ι' := ι') (g.be x y) = g.be (rho x) (rho y) := by sorry
