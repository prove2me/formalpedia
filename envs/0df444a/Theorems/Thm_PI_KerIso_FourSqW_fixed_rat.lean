-- Prove2me | Theorems.Thm_PI_KerIso_FourSqW_fixed_rat
-- name    : PI.KerIso.FourSqW.fixed_rat
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:35:07.851807+00:00
-- url     : https://prove2.me/theorems/1378f0e2-daa5-5bb3-83bf-1df19bb82926
-- title:
--   Four Sq W: fixed rat
-- statement:
--   The Four Sq W construction uses the fixed rat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FourSquareQuaternions/OrthogonalDiagonal.lean#L48-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FourSquareQuaternions/OrthogonalDiagonal.lean#L48-L74

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

theorem PI.KerIso.FourSqW.fixed_rat (cj : E ≃ₐ[ℚ] E) (hc : IsConj K cj) (h2 : finrank ℚ K = 2) (k : K)
    (hk : cj (algebraMap K E k) = algebraMap K E k) : ∃ r : ℚ, k = (r : K) := by sorry
