-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_sat_zsmul
-- name    : PI.UnitaryGroupMassFormula.UnimodLocStd.rep_sat_zsmul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:22:10.686865+00:00
-- url     : https://prove2.me/theorems/f73ee048-d2bf-4f1a-93e2-93efb0f0678a
-- title:
--   Unimod Loc Std: rep sat zsmul
-- statement:
--   The Unimod Loc Std construction uses the rep sat zsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/RepSingleSat.lean#L15-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/RepSingleSat.lean#L15-L20

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

theorem PI.UnitaryGroupMassFormula.UnimodLocStd.rep_sat_zsmul {m : Type} (l : ℕ) (Λ : AddSubgroup (m → ℂ)) {v : m → ℂ} (hv : SatMem l Λ v) (r : ℤ) :
    SatMem l Λ ((r : ℂ) • v) := by sorry
