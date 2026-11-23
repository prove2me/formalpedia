-- Prove2me | Theorems.Thm_PI_AddIntG_Wk_lamA_wser_mem
-- name    : PI.AddIntG.Wk.lamA_wser_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:15:22.134256+00:00
-- url     : https://prove2.me/theorems/0ce92492-ebb9-452e-b4e7-45f419a157fb
-- title:
--   Wk: lam A wser mem
-- statement:
--   The Wk construction uses the lam A wser mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/CoeffWSeriesVarZero.lean#L76-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/CoeffWSeriesVarZero.lean#L76-L80

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffPowMemS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffWSeriesVarZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.AddIntG PI.AddIntG.Wk
variable {p : ℕ} [Fact p.Prime]

theorem PI.AddIntG.Wk.lamA_wser_mem {S : Subring ℂ_[p]} {wq : PowerSeries ℂ_[p]} (hS : ∀ n, PowerSeries.coeff n wq ∈ S)
    (n : ℕ) : PowerSeries.coeff n (wser wq) ∈ S := by sorry
