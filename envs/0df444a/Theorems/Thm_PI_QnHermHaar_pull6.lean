-- Prove2me | Theorems.Thm_PI_QnHermHaar_pull6
-- name    : PI.QnHermHaar.pull6
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T16:08:43.679021+00:00
-- url     : https://prove2.me/theorems/4464db9a-9e84-4f35-b411-6d495639c350
-- title:
--   Qn Herm Haar: pull6
-- statement:
--   The Qn Herm Haar construction uses the pull6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/GeneralSecondMinorExpansion.lean#L78-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/GeneralSecondMinorExpansion.lean#L78-L88

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_SumFourCommVersion
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_GeneralSecondMinorExpansion
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

theorem PI.QnHermHaar.pull6 {A : Type*} [AddCommMonoid A] {m : ℕ} (f : Fin m → Fin m → Fin m → Fin m → Fin m → Fin m → A) :
    ∑ l, ∑ p, ∑ i, ∑ i', ∑ j, ∑ j', f l p i i' j j' = ∑ i, ∑ i', ∑ j, ∑ j', ∑ l, ∑ p, f l p i i' j j' := by sorry
