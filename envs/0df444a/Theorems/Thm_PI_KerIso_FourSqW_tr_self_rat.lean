-- Prove2me | Theorems.Thm_PI_KerIso_FourSqW_tr_self_rat
-- name    : PI.KerIso.FourSqW.tr_self_rat
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:34:02.873091+00:00
-- url     : https://prove2.me/theorems/36d6db4f-0105-4c9d-90bf-f1b6e12d41bc
-- title:
--   Four Sq W: tr self rat
-- statement:
--   The Four Sq W construction uses the tr self rat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FourSquareQuaternions/OrthogonalDiagonal.lean#L104-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FourSquareQuaternions/OrthogonalDiagonal.lean#L104-L118

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

theorem PI.KerIso.FourSqW.tr_self_rat (cj : E ≃ₐ[ℚ] E) (hc : IsConj K cj) (h2 : finrank ℚ K = 2)
    (hpos : ∀ x : E, x ≠ 0 → 0 < Algebra.trace ℚ E (x * cj x)) (x : E) (hx : x ≠ 0) :
    ∃ r : ℚ, 0 < r ∧ Algebra.trace K E (x * cj x) = (r : K) := by sorry
