-- Prove2me | Theorems.Thm_PI_KerIso_FourSqW_conjK_apply
-- name    : PI.KerIso.FourSqW.conjK_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:34:55.395969+00:00
-- url     : https://prove2.me/theorems/70b3c40e-39ca-5fb0-b0b0-987303e85497
-- title:
--   Four Sq W: conj K apply
-- statement:
--   The Four Sq W construction uses the conj K apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FourSquareQuaternions/OrthogonalDiagonal.lean#L34-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FourSquareQuaternions/OrthogonalDiagonal.lean#L34-L34

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

theorem PI.KerIso.FourSqW.conjK_apply (cj : E ≃ₐ[ℚ] E) (hc : IsConj K cj) (k : K) : conjK cj hc k = conjFun cj hc k := by sorry
