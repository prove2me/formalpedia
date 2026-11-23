-- Prove2me | Theorems.Thm_PI_FglPhSplit_Wk_rho_psubst
-- name    : PI.FglPhSplit.Wk.rho_psubst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:43:10.330125+00:00
-- url     : https://prove2.me/theorems/efb5677f-ba17-4bee-b666-a8b0b123b6ea
-- title:
--   Wk: rho psubst
-- statement:
--   The Wk construction uses the rho psubst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupSplitting/ExpCongruenceExtendsToSum.lean#L94-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupSplitting/ExpCongruenceExtendsToSum.lean#L94-L100

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

theorem PI.FglPhSplit.Wk.rho_psubst (P : PowerSeries K) {y : MvPowerSeries (ι ⊕ ι) K}
    (hy : MvPowerSeries.constantCoeff y = 0) :
    rho (ι' := ι') (PowerSeries.subst y P) = PowerSeries.subst (rho (ι' := ι') y) P := by sorry
