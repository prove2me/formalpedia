-- Prove2me | Theorems.Thm_PI_WADVR_big_one_add_pow
-- name    : PI.WADVR.big_one_add_pow
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:42:58.315465+00:00
-- url     : https://prove2.me/theorems/1b85b930-6381-4c8a-9960-c8480b7f842e
-- title:
--   WADVR: big one add pow
-- statement:
--   The WADVR construction uses the big one add pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeakApproximationDVR/SmOneOfNotIsUnit.lean#L149-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeakApproximationDVR/SmOneOfNotIsUnit.lean#L149-L161

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_SmOneOfNotIsUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WADVR
variable {W Q : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Q]
  [Algebra W Q] [IsFractionRing W Q]
variable {ϖ : W}

theorem PI.WADVR.big_one_add_pow (hϖ : Irreducible ϖ) {q : Q} (h0 : q ≠ 0) (h : Sm Q ϖ 1 q⁻¹) {r : ℕ}
    (hr : 1 ≤ r) : 1 + q ^ r ≠ 0 ∧ Sm Q ϖ r (1 + q ^ r)⁻¹ := by sorry
