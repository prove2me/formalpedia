-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_H_int
-- name    : PI.UnitaryGroupMassFormula.UnimodLocStd.rep_H_int
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:14:17.476046+00:00
-- url     : https://prove2.me/theorems/aab6df87-b4b8-454c-9a46-dab37e1cf740
-- title:
--   Unimod Loc Std: rep H int
-- statement:
--   The Unimod Loc Std construction uses the rep H int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/RepHSelfInt.lean#L40-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/RepHSelfInt.lean#L40-L78

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepArith
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepHSelfInt
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
variable (m : Type) [Fintype m] [DecidableEq m]

theorem PI.UnitaryGroupMassFormula.UnimodLocStd.rep_H_int (hOK : CmOK a b c d) (Λ : AddSubgroup (m → ℂ))
    (hΛ : IsSelfDual (stdH (cmL a b d ha hd lam hlam) m) Λ) (hθ : ∀ z ∈ Λ, cmTheta b d • z ∈ Λ)
    {x y : m → ℂ} (hx : x ∈ Λ) (hy : y ∈ Λ) :
    ∃ n c₂ : ℤ, stdH (cmL a b d ha hd lam hlam) m x y =
      repKappa a b d ha hd lam hlam * ((n : ℂ) - c₂ * conj (cmTheta b d)) ∧
      (stdH (cmL a b d ha hd lam hlam) m x y).im = c₂ := by sorry
