-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_ProdUnitInert_norm_conic_eq_one
-- name    : PI.UnitaryGroupMassFormula.ProdUnitInert.norm_conic_eq_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:32:26.250772+00:00
-- url     : https://prove2.me/theorems/b2bcd717-dc2b-5d27-ad33-68dc2cd14bb9
-- title:
--   Prod Unit Inert: norm conic eq one
-- statement:
--   The Prod Unit Inert construction uses the norm conic eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertUnitProduct/NatCastNormLeOne.lean#L74-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertUnitProduct/NatCastNormLeOne.lean#L74-L106

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertUnitProduct_NatCastNormLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ProdUnitInert
variable {p : ℕ} [Fact p.Prime]

theorem PI.UnitaryGroupMassFormula.ProdUnitInert.norm_conic_eq_one (d : ℕ) (hd : ¬ IsSquare (((-(d : ℤ) : ℤ) : ZMod p))) (x y : ℚ)
    (hxy : x ^ 2 + d * y ^ 2 = 1) (γ : ℂ_[p]) (hγ : γ ^ 2 = -(d : ℂ_[p])) :
    ‖(x : ℂ_[p]) + y * γ‖ = 1 := by sorry
