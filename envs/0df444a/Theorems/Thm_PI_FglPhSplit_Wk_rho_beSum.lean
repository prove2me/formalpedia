-- Prove2me | Theorems.Thm_PI_FglPhSplit_Wk_rho_beSum
-- name    : PI.FglPhSplit.Wk.rho_beSum
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:29:46.559518+00:00
-- url     : https://prove2.me/theorems/c62075c2-02c2-5cd4-bcbd-f8214806045c
-- title:
--   Wk: rho be Sum
-- statement:
--   The Wk construction uses the rho be Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupSplitting/ExpCongruenceExtendsToSum.lean#L178-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupSplitting/ExpCongruenceExtendsToSum.lean#L178-L184

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

theorem PI.FglPhSplit.Wk.rho_beSum :
    rho (ι' := ι') (g.beSum ι) = ∑ e : ι, g.be (MvPowerSeries.X (Sum.inl (Sum.inl e)))
      (MvPowerSeries.X (Sum.inl (Sum.inr e))) := by sorry
