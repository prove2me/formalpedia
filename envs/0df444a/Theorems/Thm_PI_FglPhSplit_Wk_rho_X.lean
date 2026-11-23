-- Prove2me | Theorems.Thm_PI_FglPhSplit_Wk_rho_X
-- name    : PI.FglPhSplit.Wk.rho_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:25:47.91597+00:00
-- url     : https://prove2.me/theorems/369e0497-0477-4569-b9f9-2b2a25a5cc00
-- title:
--   Wk: rho X
-- statement:
--   The Wk construction uses the rho X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupSplitting/ExpCongruenceExtendsToSum.lean#L102-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupSplitting/ExpCongruenceExtendsToSum.lean#L102-L104

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

theorem PI.FglPhSplit.Wk.rho_X (j : ι ⊕ ι) :
    rho (ι' := ι') (MvPowerSeries.X j : MvPowerSeries (ι ⊕ ι) K) = MvPowerSeries.X (Sum.inl j) := by sorry
