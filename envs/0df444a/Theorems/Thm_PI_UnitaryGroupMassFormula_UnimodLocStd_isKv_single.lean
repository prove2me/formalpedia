-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_isKv_single
-- name    : PI.UnitaryGroupMassFormula.UnimodLocStd.isKv_single
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:12:52.969786+00:00
-- url     : https://prove2.me/theorems/fe3d3bf2-8b85-47c1-93bf-15731c011d8a
-- title:
--   Unimod Loc Std: is Kv single
-- statement:
--   The Unimod Loc Std construction uses the is Kv single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/CommOfBounded.lean#L94-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/CommOfBounded.lean#L94-L100

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_IsKTheta
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_CommOfBounded
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

theorem PI.UnitaryGroupMassFormula.UnimodLocStd.isKv_single {w : ℂ} (hw : IsK b d (w / lam)) (i : m) : IsKv b d lam (Pi.single i w) := by sorry
