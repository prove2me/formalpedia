-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_theta_alpha_eq
-- name    : PI.UnitaryGroupMassFormula.UnimodLocStd.theta_alpha_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:41:36.777008+00:00
-- url     : https://prove2.me/theorems/e90031db-2829-4411-aecd-4e1bc6f4804d
-- title:
--   Unimod Loc Std: theta alpha eq
-- statement:
--   The Unimod Loc Std construction uses the theta alpha eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/SatStdOfAll.lean#L35-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/SatStdOfAll.lean#L35-L42

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

theorem PI.UnitaryGroupMassFormula.UnimodLocStd.theta_alpha_eq (hn : cmTheta b d * (b - cmTheta b d) = (a : ℂ) * c) (x y : ℤ) :
    cmTheta b d * (lam * ((x * a : ℂ) + y * cmTheta b d)) =
      ((-y * c : ℤ) : ℝ) • (cmL a b d ha hd lam hlam).ω₁ +
        ((x * a + y * b : ℤ) : ℝ) • (cmL a b d ha hd lam hlam).ω₂ := by sorry
