-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_isKv_smul
-- name    : PI.UnitaryGroupMassFormula.UnimodLocStd.isKv_smul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:33:47.761411+00:00
-- url     : https://prove2.me/theorems/bdc300d2-36f5-4cfd-b423-1000aee0d148
-- title:
--   Unimod Loc Std: is Kv smul
-- statement:
--   The Unimod Loc Std construction uses the is Kv smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/CommOfBounded.lean#L88-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/CommOfBounded.lean#L88-L92

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

theorem PI.UnitaryGroupMassFormula.UnimodLocStd.isKv_smul {e : ℤ} (hn : cmTheta b d * (b - cmTheta b d) = (e : ℂ)) {t : ℂ} {v : m → ℂ}
    (ht : IsK b d t) (hv : IsKv b d lam v) : IsKv b d lam (t • v) := by sorry
