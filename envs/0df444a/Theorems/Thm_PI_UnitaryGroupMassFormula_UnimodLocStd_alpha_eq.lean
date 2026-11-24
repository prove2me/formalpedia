-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_alpha_eq
-- name    : PI.UnitaryGroupMassFormula.UnimodLocStd.alpha_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:32:01.606151+00:00
-- url     : https://prove2.me/theorems/e0348d35-cd37-4144-bdf8-8e14a7767b4c
-- title:
--   Unimod Loc Std: alpha eq
-- statement:
--   The Unimod Loc Std construction uses the alpha eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/SatStdOfAll.lean#L27-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/SatStdOfAll.lean#L27-L33

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_ExistsGoodForm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_SatStdOfAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
variable {a : ℕ} {b c : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}
variable {m : Type*} [Fintype m] [DecidableEq m]

theorem PI.UnitaryGroupMassFormula.UnimodLocStd.alpha_eq (x y : ℤ) :
    lam * ((x * a : ℂ) + y * cmTheta b d) =
      (x : ℝ) • (cmL a b d ha hd lam hlam).ω₁ + (y : ℝ) • (cmL a b d ha hd lam hlam).ω₂ := by sorry
