-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_H_zT
-- name    : PI.UnitaryGroupMassFormula.UnimodLocStd.rep_H_zT
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:22:59.658236+00:00
-- url     : https://prove2.me/theorems/d9f15c11-420b-4220-b433-c0119bef8447
-- title:
--   Unimod Loc Std: rep H z T
-- statement:
--   The Unimod Loc Std construction uses the rep H z T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/RepSingleSat.lean#L208-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/RepSingleSat.lean#L208-L219

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepHSelfInt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepExact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepSingleSat
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
variable (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)
  (m : Type) [Fintype m] [DecidableEq m]

theorem PI.UnitaryGroupMassFormula.UnimodLocStd.rep_H_zT (T : Finset m) {z y : m → ℂ} (hz : ∀ j ∈ T, z j = 0) :
    stdH (cmL a b d ha hd lam hlam) m z (zT T y) = stdH (cmL a b d ha hd lam hlam) m z y := by sorry
