-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_ClassNumImQInt_intBasis
-- name    : PI.UnitaryGroupMassFormula.ClassNumImQInt.intBasis
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:39:11.223347+00:00
-- url     : https://prove2.me/theorems/9fcbcef7-a942-4b67-8fd2-8ff7386b1672
-- title:
--   Class Num Im QInt: int Basis
-- statement:
--   The Class Num Im QInt construction uses the int Basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ClassNumberIntegrality/HalfIntegral.lean#L25-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ClassNumberIntegrality/HalfIntegral.lean#L25-L38

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

theorem PI.UnitaryGroupMassFormula.ClassNumImQInt.intBasis : PI.ClassNumImQ.IntBasis := by sorry
