-- Prove2me | Theorems.Thm_PI_FglPhSplit_Wk_simeqW_rho
-- name    : PI.FglPhSplit.Wk.simeqW_rho
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:29:54.475751+00:00
-- url     : https://prove2.me/theorems/601c946a-1597-4f2f-b809-d5dabea04261
-- title:
--   Wk: simeq W rho
-- statement:
--   The Wk construction uses the simeq W rho property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupSplitting/ExpCongruenceExtendsToSum.lean#L187-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupSplitting/ExpCongruenceExtendsToSum.lean#L187-L212

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
omit hex0 hl0

theorem PI.FglPhSplit.Wk.simeqW_rho [CharZero K] {W : Subring K} {f h : MvPowerSeries (ι ⊕ ι) K}
    (hfh : SimeqW W f h) : SimeqW W (rho (ι' := ι') f) (rho h) := by sorry
