-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_SimeqPdInt_pd_eq
-- name    : PI.UnitaryGroupMassFormula.SimeqPdInt.pd_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:39:57.25606+00:00
-- url     : https://prove2.me/theorems/205748eb-f5ed-5d6d-94e7-93f0934b4f1b
-- title:
--   Simeq Pd Int: pd eq
-- statement:
--   The Simeq Pd Int construction uses the pd eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialCoefficientSeries/CoeffExpMvEqTs.lean#L13-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialCoefficientSeries/CoeffExpMvEqTs.lean#L13-L18

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SimeqPdInt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubeFormalIdentities_CoeffPowMulPowEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialCoefficientSeries_CoeffExpMvEqTs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.SimeqPdInt
variable {p : ℕ} [Fact p.Prime] {σ : Type*}

theorem PI.UnitaryGroupMassFormula.SimeqPdInt.pd_eq [DecidableEq σ] (k : σ) (F : MvPowerSeries σ ℂ_[p]) :
    PI.SimeqPdInt.pd k F = pderiv ℂ_[p] k F := by sorry
