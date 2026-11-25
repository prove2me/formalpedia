-- Prove2me | Theorems.Thm_PI_QnHermHaar_swap4a
-- name    : PI.QnHermHaar.swap4a
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:38:54.013982+00:00
-- url     : https://prove2.me/theorems/e06d6451-dc67-413d-a6b0-bedd403cd9c7
-- title:
--   Qn Herm Haar: swap4a
-- statement:
--   The Qn Herm Haar construction uses the swap4a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/LowerRightNeZeroOfUpperRightZero.lean#L14-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/LowerRightNeZeroOfUpperRightZero.lean#L14-L20

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

theorem PI.QnHermHaar.swap4a {A : Type*} [AddCommMonoid A] {p q : ℕ} (F : Fin p → Fin q → Fin p → Fin q → A) :
    ∑ i, ∑ k, ∑ j, ∑ l, F i k j l = ∑ j, ∑ i, ∑ l, ∑ k, F i k j l := by sorry
