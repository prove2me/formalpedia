-- Prove2me | Theorems.Thm_PI_FglTriFactor_Wk_subst_pt
-- name    : PI.FglTriFactor.Wk.subst_pt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:26:42.786798+00:00
-- url     : https://prove2.me/theorems/6229c6cc-dc4f-40dd-96c4-3abd80f38922
-- title:
--   Wk: subst pt
-- statement:
--   The Wk construction uses the subst pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupTriangles/PairSubstXZero.lean#L44-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupTriangles/PairSubstXZero.lean#L44-L47

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglTriFactor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_CoeffSubstUpdZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_PairSubstXZero
import Theorems.Thm_PI_AddIntG_Wk_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_mvsubst_mem_SerS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FglTriFactor PI.FglTriFactor.Wk
open PI.AddIntG.Wk (SerS mem_SerS mvsubst_mem_SerS)
variable {p : ℕ} [Fact p.Prime]
variable {l ex : PowerSeries ℂ_[p]} {σ τ : Type*}

theorem PI.FglTriFactor.Wk.subst_pt {b : σ → MvPowerSeries τ ℂ_[p]} (hb : MvPowerSeries.HasSubst b) {a : MvPowerSeries σ ℂ_[p]}
    (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.subst b (pt ex a) = pt ex (MvPowerSeries.subst b a) := by sorry
