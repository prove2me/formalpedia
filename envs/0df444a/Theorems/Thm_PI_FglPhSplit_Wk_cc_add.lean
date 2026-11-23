-- Prove2me | Theorems.Thm_PI_FglPhSplit_Wk_cc_add
-- name    : PI.FglPhSplit.Wk.cc_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:43:54.056317+00:00
-- url     : https://prove2.me/theorems/14783419-f403-4824-a02e-8af57af38cd4
-- title:
--   Wk: cc add
-- statement:
--   The Wk construction uses the cc add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupSplitting/ExpCongruenceExtendsToSum.lean#L127-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupSplitting/ExpCongruenceExtendsToSum.lean#L127-L130

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

theorem PI.FglPhSplit.Wk.cc_add {σ : Type} {x y : MvPowerSeries σ K} (hx : MvPowerSeries.constantCoeff x = 0)
    (hy : MvPowerSeries.constantCoeff y = 0) : MvPowerSeries.constantCoeff (g.add x y) = 0 := by sorry
