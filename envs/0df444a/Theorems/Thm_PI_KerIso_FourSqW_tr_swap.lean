-- Prove2me | Theorems.Thm_PI_KerIso_FourSqW_tr_swap
-- name    : PI.KerIso.FourSqW.tr_swap
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:44:42.349941+00:00
-- url     : https://prove2.me/theorems/1b62e703-94fe-460f-887c-1aa2e6ec7fad
-- title:
--   Four Sq W: tr swap
-- statement:
--   The Four Sq W construction uses the tr swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FourSquareQuaternions/OrthogonalDiagonal.lean#L87-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FourSquareQuaternions/OrthogonalDiagonal.lean#L87-L89

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

theorem PI.KerIso.FourSqW.tr_swap (cj : E ≃ₐ[ℚ] E) (hc : IsConj K cj) (x y : E) :
    algebraMap K E (Algebra.trace K E (y * cj x)) = cj (algebraMap K E (Algebra.trace K E (x * cj y))) := by sorry
