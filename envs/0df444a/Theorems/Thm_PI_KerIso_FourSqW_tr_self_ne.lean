-- Prove2me | Theorems.Thm_PI_KerIso_FourSqW_tr_self_ne
-- name    : PI.KerIso.FourSqW.tr_self_ne
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:34:28.646798+00:00
-- url     : https://prove2.me/theorems/608e4894-edeb-41c4-94b0-cec00e77122e
-- title:
--   Four Sq W: tr self ne
-- statement:
--   The Four Sq W construction uses the tr self ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FourSquareQuaternions/OrthogonalDiagonal.lean#L96-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FourSquareQuaternions/OrthogonalDiagonal.lean#L96-L102

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

theorem PI.KerIso.FourSqW.tr_self_ne (cj : E ≃ₐ[ℚ] E) (hpos : ∀ x : E, x ≠ 0 → 0 < Algebra.trace ℚ E (x * cj x))
    (x : E) (hx : x ≠ 0) : Algebra.trace K E (x * cj x) ≠ 0 := by sorry
