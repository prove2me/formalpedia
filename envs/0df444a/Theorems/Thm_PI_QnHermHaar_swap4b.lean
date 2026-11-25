-- Prove2me | Theorems.Thm_PI_QnHermHaar_swap4b
-- name    : PI.QnHermHaar.swap4b
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T06:00:58.039965+00:00
-- url     : https://prove2.me/theorems/6d1ce195-35e0-4c46-8f41-9c08e627c75a
-- title:
--   Qn Herm Haar: swap4b
-- statement:
--   The Qn Herm Haar construction uses the swap4b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/LowerRightNeZeroOfUpperRightZero.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/LowerRightNeZeroOfUpperRightZero.lean#L22-L24

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_NestedMinorExpansionOneZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_LowerRightNeZeroOfUpperRightZero
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

theorem PI.QnHermHaar.swap4b {A : Type*} [AddCommMonoid A] {p q : ℕ} (F : Fin p → Fin q → Fin p → Fin q → A) :
    ∑ i, ∑ k, ∑ j, ∑ l, F i k j l = ∑ i, ∑ j, ∑ k, ∑ l, F i k j l := by sorry
