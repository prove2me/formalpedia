-- Prove2me | Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_UnimodLocStd_not_dvd_mul__02e58b10b277
-- name    : P2M_PI_UnitaryGroupMassFormula_UnimodLocStd_not_dvd_mul__02e58b10b277
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:33:19.009245+00:00
-- url     : https://prove2.me/theorems/29809c10-f8cd-4182-b0bd-e1146950ee4c
-- title:
--   P2 M PI Unitary Group Mass Formula Unimod Loc Std not dvd mul  02e58b10b277: P2 M PI Unitary Group Mass Formula Unimod Loc Std not dvd mul  02e58b10b277
-- statement:
--   The P2 M PI Unitary Group Mass Formula Unimod Loc Std not dvd mul  02e58b10b277 construction uses the P2 M PI Unitary Group Mass Formula Unimod Loc Std not dvd mul  02e58b10b277 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/HNsmulNsmul.lean#L17-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/HNsmulNsmul.lean#L17-L22

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepSingleSat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_DescentStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_HNsmulNsmul
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

theorem P2M_PI_UnitaryGroupMassFormula_UnimodLocStd_not_dvd_mul__02e58b10b277 {l : ℕ} (hl : l.Prime) {u v : ℤ} (hu : ¬ (l : ℤ) ∣ u) (hv : ¬ (l : ℤ) ∣ v) :
    ¬ (l : ℤ) ∣ u * v := by sorry

alias «PI».«UnitaryGroupMassFormula».«UnimodLocStd».«not_dvd_mul'» := P2M_PI_UnitaryGroupMassFormula_UnimodLocStd_not_dvd_mul__02e58b10b277
