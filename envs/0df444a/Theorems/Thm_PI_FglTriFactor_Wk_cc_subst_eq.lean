-- Prove2me | Theorems.Thm_PI_FglTriFactor_Wk_cc_subst_eq
-- name    : PI.FglTriFactor.Wk.cc_subst_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:55:24.50784+00:00
-- url     : https://prove2.me/theorems/2b5bacd0-f65d-4557-a7de-bf65dae771bb
-- title:
--   Wk: cc subst eq
-- statement:
--   The Wk construction uses the cc subst eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupTriangles/PairSubstXZero.lean#L131-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupTriangles/PairSubstXZero.lean#L131-L139

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
variable {τ : Type*}

theorem PI.FglTriFactor.Wk.cc_subst_eq {σ : Type*} {a : σ → MvPowerSeries τ ℂ_[p]} (hA : MvPowerSeries.HasSubst a)
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (f : MvPowerSeries σ ℂ_[p]) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) = MvPowerSeries.constantCoeff f := by sorry
