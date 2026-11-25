-- Prove2me | Theorems.Thm_PI_KerIso_FourSqW_exists_orth
-- name    : PI.KerIso.FourSqW.exists_orth
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:33:20.574707+00:00
-- url     : https://prove2.me/theorems/33952358-56e8-44b2-9653-231002a707c2
-- title:
--   Four Sq W: exists orth
-- statement:
--   The Four Sq W construction uses the exists orth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FourSquareQuaternions/OrthogonalDiagonal.lean#L120-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FourSquareQuaternions/OrthogonalDiagonal.lean#L120-L155

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_FourSqOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_OrthogonalDiagonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Module
open PI PI.KerIso PI.KerIso.FourSqW
variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]

theorem PI.KerIso.FourSqW.exists_orth (cj : E ≃ₐ[ℚ] E) (hc : IsConj K cj)
    (hpos : ∀ x : E, x ≠ 0 → 0 < Algebra.trace ℚ E (x * cj x)) :
    ∀ m : ℕ, m ≤ finrank K E → ∃ e : Fin m → E, (∀ i, e i ≠ 0) ∧
      ∀ i j, i ≠ j → Algebra.trace K E (e i * cj (e j)) = 0 := by sorry
