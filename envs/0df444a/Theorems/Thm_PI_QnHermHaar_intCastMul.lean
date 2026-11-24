-- Prove2me | Theorems.Thm_PI_QnHermHaar_intCastMul
-- name    : PI.QnHermHaar.intCastMul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T15:16:46.708906+00:00
-- url     : https://prove2.me/theorems/df2e6bf7-98e7-4ee4-9b69-45bc9b5cc6c2
-- title:
--   Qn Herm Haar: int Cast Mul
-- statement:
--   The Qn Herm Haar construction uses the int Cast Mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/NestedMinorExpansionOneZero.lean#L86-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/NestedMinorExpansionOneZero.lean#L86-L87

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_NestedMinorExpansionOneZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.QnHermHaar
open Formalism.REAL Formalism.FourierDecayAlt.Q

theorem PI.QnHermHaar.intCastMul {A : Type*} [Ring A] [Algebra ℂ A] (z : ℤ) (X : A) : (z : A) * X = (z : ℂ) • X := by sorry
