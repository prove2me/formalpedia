-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_sat_norm
-- name    : PI.UnitaryGroupMassFormula.UnimodLocStd.sat_norm
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:41:51.897425+00:00
-- url     : https://prove2.me/theorems/ea684621-9ec4-4341-ade3-02eb735fc1f1
-- title:
--   Unimod Loc Std: sat norm
-- statement:
--   The Unimod Loc Std construction uses the sat norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/HNsmulNsmul.lean#L46-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/HNsmulNsmul.lean#L46-L59

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
variable {a b c d ha hd lam hlam m}

theorem PI.UnitaryGroupMassFormula.UnimodLocStd.sat_norm (hOK : CmOK a b c d) {Λ : AddSubgroup (m → ℂ)}
    (hΛ : IsSelfDual (stdH (cmL a b d ha hd lam hlam) m) Λ) (hθ : ∀ z ∈ Λ, cmTheta b d • z ∈ Λ)
    {l : ℕ} (hl : l.Prime) {v : m → ℂ} (hv : SatMem l Λ v) :
    ∃ p q : ℤ, ¬ (l : ℤ) ∣ q ∧ stdH (cmL a b d ha hd lam hlam) m v v = repKappa a b d ha hd lam hlam * p / q := by sorry
