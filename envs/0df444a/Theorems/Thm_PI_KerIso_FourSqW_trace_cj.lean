-- Prove2me | Theorems.Thm_PI_KerIso_FourSqW_trace_cj
-- name    : PI.KerIso.FourSqW.trace_cj
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:34:09.559125+00:00
-- url     : https://prove2.me/theorems/62abece5-3993-485b-ab42-a77c5537f35d
-- title:
--   Four Sq W: trace cj
-- statement:
--   The Four Sq W construction uses the trace cj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FourSquareQuaternions/OrthogonalDiagonal.lean#L36-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FourSquareQuaternions/OrthogonalDiagonal.lean#L36-L46

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

theorem PI.KerIso.FourSqW.trace_cj (cj : E ≃ₐ[ℚ] E) (hc : IsConj K cj) (z : E) :
    algebraMap K E (Algebra.trace K E (cj z)) = cj (algebraMap K E (Algebra.trace K E z)) := by sorry
