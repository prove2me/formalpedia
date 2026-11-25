-- Prove2me | Theorems.Thm_PI_ScPiFrameW_re_star_mul_mul
-- name    : PI.ScPiFrameW.re_star_mul_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:21:27.907629+00:00
-- url     : https://prove2.me/theorems/e09c12ac-d50e-4cbe-a716-38ad88c311f6
-- title:
--   Sc Pi Frame W: re star mul mul
-- statement:
--   The Sc Pi Frame W construction uses the re star mul mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianFrameExistence/HJSumSmulRight.lean#L91-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianFrameExistence/HJSumSmulRight.lean#L91-L92

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianFrameExistence_HJSumSmulRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.ScPiFrameW
open PI.ScPiExists
variable {n : ℕ}

theorem PI.ScPiFrameW.re_star_mul_mul (a b : ℂ) : (star a * (a * b)).re = Complex.normSq a * b.re := by sorry
