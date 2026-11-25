-- Prove2me | Theorems.Thm_PI_FglPhSplit_Wk_rho_lin
-- name    : PI.FglPhSplit.Wk.rho_lin
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:29:51.953311+00:00
-- url     : https://prove2.me/theorems/588e1c1f-c999-443a-9438-5f16425dcab8
-- title:
--   Wk: rho lin
-- statement:
--   The Wk construction uses the rho lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupSplitting/ExpCongruenceExtendsToSum.lean#L146-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupSplitting/ExpCongruenceExtendsToSum.lean#L146-L159

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

theorem PI.FglPhSplit.Wk.rho_lin {κ' : Type} [Fintype κ'] (c : κ' → K) (w : κ' → MvPowerSeries (ι ⊕ ι) K)
    (hw : ∀ j, MvPowerSeries.constantCoeff (w j) = 0) :
    rho (ι' := ι') (g.lin c w) = g.lin c (fun j => rho (w j)) := by sorry
