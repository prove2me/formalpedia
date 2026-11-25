-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_ClassNumImQInt_half_integral
-- name    : PI.UnitaryGroupMassFormula.ClassNumImQInt.half_integral
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:39:16.764072+00:00
-- url     : https://prove2.me/theorems/26f33e8b-3c7d-4405-8131-e5316b5e345b
-- title:
--   Class Num Im QInt: half integral
-- statement:
--   The Class Num Im QInt construction uses the half integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ClassNumberIntegrality/HalfIntegral.lean#L17-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ClassNumberIntegrality/HalfIntegral.lean#L17-L23

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ClassNumImQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticDifference_QuadraticDifferenceForm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ClassNumberIntegrality_HalfIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ClassNumImQInt
open NumberField Polynomial

theorem PI.UnitaryGroupMassFormula.ClassNumImQInt.half_integral {K : Type} [Field K] [NumberField K] (d : ℕ) (b : K) (hd : d % 4 = 3)
    (hb : b ^ 2 = -(d : K)) : IsIntegral ℤ ((1 + b) / 2) := by sorry
