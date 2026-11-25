-- Prove2me | Theorems.Thm_PI_FglPhSplit_Wk_rho_PhOn
-- name    : PI.FglPhSplit.Wk.rho_PhOn
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:30:19.90701+00:00
-- url     : https://prove2.me/theorems/689ced0f-9fd9-4d3d-9988-250405917c86
-- title:
--   Wk: rho Ph On
-- statement:
--   The Wk construction uses the rho Ph On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupSplitting/ExpCongruenceExtendsToSum.lean#L161-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupSplitting/ExpCongruenceExtendsToSum.lean#L161-L176

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

theorem PI.FglPhSplit.Wk.rho_PhOn {κ : Type} [Fintype κ] (b : ι ⊕ ι → κ → K × K) :
    rho (ι' := ι') (g.PhOn b) = g.PhV b (fun e => MvPowerSeries.X (Sum.inl e)) := by sorry
