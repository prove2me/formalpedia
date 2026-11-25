-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_stdH_symm
-- name    : PI.UnitaryGroupMassFormula.UnimodLocStd.stdH_symm
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:41:20.08293+00:00
-- url     : https://prove2.me/theorems/a0667060-5aa9-5ff3-b71f-c5f058bacfb8
-- title:
--   Unimod Loc Std: std H symm
-- statement:
--   The Unimod Loc Std construction uses the std H symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/StdHSingleZero.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/StdHSingleZero.lean#L12-L16

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

theorem PI.UnitaryGroupMassFormula.UnimodLocStd.stdH_symm (L : PeriodPair) (x y : m → ℂ) : stdH L m y x = conj (stdH L m x y) := by sorry
