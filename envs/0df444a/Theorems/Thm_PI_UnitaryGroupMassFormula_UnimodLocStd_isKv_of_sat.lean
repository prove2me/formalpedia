-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_isKv_of_sat
-- name    : PI.UnitaryGroupMassFormula.UnimodLocStd.isKv_of_sat
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:35:35.042571+00:00
-- url     : https://prove2.me/theorems/76a6752a-ac05-4d5b-ad83-70a3e6463d61
-- title:
--   Unimod Loc Std: is Kv of sat
-- statement:
--   The Unimod Loc Std construction uses the is Kv of sat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/ExistsIsometryMemLocalizedAtSingle.lean#L12-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/ExistsIsometryMemLocalizedAtSingle.lean#L12-L24

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_StdHSingleZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_ExistsIsometryMemLocalizedAtSingle
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

theorem PI.UnitaryGroupMassFormula.UnimodLocStd.isKv_of_sat {m : Type*} [Fintype m] [DecidableEq m] {l : ℕ} (hl : l.Prime) {Λ : AddSubgroup (m → ℂ)}
    (h1 : relIdx (stdLat (cmL a b d ha hd lam hlam) m) Λ ≠ 0) {v : m → ℂ} (hv : SatMem l Λ v) :
    IsKv b d lam v := by sorry
