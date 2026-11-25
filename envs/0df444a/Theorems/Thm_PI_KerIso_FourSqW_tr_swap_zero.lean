-- Prove2me | Theorems.Thm_PI_KerIso_FourSqW_tr_swap_zero
-- name    : PI.KerIso.FourSqW.tr_swap_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:33:53.148349+00:00
-- url     : https://prove2.me/theorems/185f660d-2d0b-425e-affd-eff5eb29c201
-- title:
--   Four Sq W: tr swap zero
-- statement:
--   The Four Sq W construction uses the tr swap zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FourSquareQuaternions/OrthogonalDiagonal.lean#L91-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FourSquareQuaternions/OrthogonalDiagonal.lean#L91-L94

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

theorem PI.KerIso.FourSqW.tr_swap_zero (cj : E ≃ₐ[ℚ] E) (hc : IsConj K cj) (x y : E)
    (h : Algebra.trace K E (x * cj y) = 0) : Algebra.trace K E (y * cj x) = 0 := by sorry
