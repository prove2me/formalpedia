-- Prove2me | Theorems.Thm_PI_KerFourSqW_rat_sum_four_squares
-- name    : PI.KerFourSqW.rat_sum_four_squares
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:33:04.681092+00:00
-- url     : https://prove2.me/theorems/01560b25-a668-4ca9-8431-687676dcfcc0
-- title:
--   Ker Four Sq W: rat sum four squares
-- statement:
--   The Ker Four Sq W construction uses the rat sum four squares property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FourSquareQuaternions/QuatMatTransposeMul.lean#L20-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FourSquareQuaternions/QuatMatTransposeMul.lean#L20-L33

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_QuatMatTransposeMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
open PI PI.KerFourSqW

theorem PI.KerFourSqW.rat_sum_four_squares (a : ℚ) (ha : 0 < a) :
    ∃ r₁ r₂ r₃ r₄ : ℚ, r₁ ^ 2 + r₂ ^ 2 + r₃ ^ 2 + r₄ ^ 2 = a := by sorry
