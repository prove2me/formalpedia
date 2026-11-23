-- Prove2me | Theorems.Thm_PI_FglTriFactor_Wk_subst_sub
-- name    : PI.FglTriFactor.Wk.subst_sub
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:52:40.84+00:00
-- url     : https://prove2.me/theorems/3016b6b9-9154-453d-bcdd-7a00871dbf4c
-- title:
--   Wk: subst sub
-- statement:
--   The Wk construction uses the subst sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupTriangles/PairSubstXZero.lean#L58-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupTriangles/PairSubstXZero.lean#L58-L65

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

theorem PI.FglTriFactor.Wk.subst_sub (hl : PowerSeries.constantCoeff l = 0) {b : σ → MvPowerSeries τ ℂ_[p]}
    (hb : MvPowerSeries.HasSubst b) {x y : MvPowerSeries σ ℂ_[p]}
    (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0) :
    MvPowerSeries.subst b (sub l ex x y) = sub l ex (MvPowerSeries.subst b x) (MvPowerSeries.subst b y) := by sorry
