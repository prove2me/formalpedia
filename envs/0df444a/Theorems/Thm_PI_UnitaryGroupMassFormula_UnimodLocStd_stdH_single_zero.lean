-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_stdH_single_zero
-- name    : PI.UnitaryGroupMassFormula.UnimodLocStd.stdH_single_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:41:52.510801+00:00
-- url     : https://prove2.me/theorems/89131586-55a5-43f3-8a24-feb95e73c86a
-- title:
--   Unimod Loc Std: std H single zero
-- statement:
--   The Unimod Loc Std construction uses the std H single zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/StdHSingleZero.lean#L18-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/StdHSingleZero.lean#L18-L27

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_SatStdOfAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_StdHSingleZero
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

theorem PI.UnitaryGroupMassFormula.UnimodLocStd.stdH_single_zero (L : PeriodPair) (j : m) (w : ℂ) {z : m → ℂ} (hz : z j = 0) :
    stdH L m (Pi.single j w) z = 0 := by sorry
