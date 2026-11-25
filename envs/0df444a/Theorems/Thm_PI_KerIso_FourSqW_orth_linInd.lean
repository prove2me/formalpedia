-- Prove2me | Theorems.Thm_PI_KerIso_FourSqW_orth_linInd
-- name    : PI.KerIso.FourSqW.orth_linInd
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:35:32.818532+00:00
-- url     : https://prove2.me/theorems/2f7190a9-b310-5779-b388-d22082e97678
-- title:
--   Four Sq W: orth lin Ind
-- statement:
--   The Four Sq W construction uses the orth lin Ind property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FourSquareQuaternions/OrthogonalDiagonal.lean#L157-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FourSquareQuaternions/OrthogonalDiagonal.lean#L157-L170

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

theorem PI.KerIso.FourSqW.orth_linInd {n : Type} [Fintype n] (cj : E ≃ₐ[ℚ] E)
    (hpos : ∀ x : E, x ≠ 0 → 0 < Algebra.trace ℚ E (x * cj x)) (v : n → E)
    (hv0 : ∀ i, v i ≠ 0) (hvo : ∀ i j, i ≠ j → Algebra.trace K E (v i * cj (v j)) = 0) :
    LinearIndependent K v := by sorry
