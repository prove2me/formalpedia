-- Prove2me | Theorems.Thm_PI_WfLogWork_Gv_memS
-- name    : PI.WfLogWork.Gv_memS
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:04:57.475183+00:00
-- url     : https://prove2.me/theorems/b35058f5-ad77-549d-ad1d-3829d7d16e1c
-- title:
--   Wf Log Work: Gv mem S
-- statement:
--   The Wf Log Work construction uses the Gv mem S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittLogarithm/FormalLogarithmHolds.lean#L40-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittLogarithm/FormalLogarithmHolds.lean#L40-L59

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittLogarithm_CoefWfIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_DXEqDerivative
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittLogarithm_FormalLogarithmHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WfLogWork
open PI.ExpIntWProof PI.AddIntG.Wk
variable {p : ℕ} [Fact p.Prime]

theorem PI.WfLogWork.Gv_memS {S : Subring ℂ_[p]} {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]}
    (h1 : W.a₁ ∈ S) (h2 : W.a₂ ∈ S) (h3 : W.a₃ ∈ S) (h4 : W.a₄ ∈ S) (h6 : W.a₆ ∈ S) (hW : AddIntG.IsWq W wq) :
    ((Gv W (PowerSeries.X : PowerSeries ℂ_[p]) (wser wq) : PowerSeries ℂ_[p]) : MvPowerSeries Unit ℂ_[p]) ∈
      SerS S Unit := by sorry
