-- Prove2me | Theorems.Thm_PI_QnHermHaar_general_second_minor_expansion
-- name    : PI.QnHermHaar.general_second_minor_expansion
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:38:13.525689+00:00
-- url     : https://prove2.me/theorems/3a73d075-c6da-5101-af99-c97e5a7f5d97
-- title:
--   Qn Herm Haar: general second minor expansion
-- statement:
--   The Qn Herm Haar construction uses the general second minor expansion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/GeneralSecondMinorExpansion.lean#L101-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/GeneralSecondMinorExpansion.lean#L101-L124

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

theorem PI.QnHermHaar.general_second_minor_expansion {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (W V : Fin m → A) (w : ℂ)
    (a' β' : Fin m → ℂ) :
    ∑ l, ∑ p, W l * V p * chat2A E w (Pi.single p 1) a' (Pi.single l 1) β' =
      ∑ i : Fin m, ∑ i' : Fin m, ∑ j : Fin m, ∑ j' : Fin m,
        if i < i' ∧ j < j' then
          ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ) + (j : ℕ) + (j' : ℕ))) •
            ((W i * algebraMap ℂ A (β' i') - W i' * algebraMap ℂ A (β' i)) *
              (V j * algebraMap ℂ A (a' j') - V j' * algebraMap ℂ A (a' j)) *
              qminor E (skip2 i i') (skip2 j j') w)
        else 0 := by sorry
