-- Prove2me | Theorems.Thm_PI_FglPhSplit_Wk_cc_psubst
-- name    : PI.FglPhSplit.Wk.cc_psubst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:43:14.96159+00:00
-- url     : https://prove2.me/theorems/753e17dd-caff-4f42-b07b-ba46e255af8b
-- title:
--   Wk: cc psubst
-- statement:
--   The Wk construction uses the cc psubst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupSplitting/ExpCongruenceExtendsToSum.lean#L114-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupSplitting/ExpCongruenceExtendsToSum.lean#L114-L121

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

theorem PI.FglPhSplit.Wk.cc_psubst {σ : Type} (P : PowerSeries K) (hP : PowerSeries.constantCoeff P = 0)
    {y : MvPowerSeries σ K} (hy : MvPowerSeries.constantCoeff y = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst y P) = 0 := by sorry
