-- Prove2me | Theorems.Thm_PI_QnHermHaar_chatAa
-- name    : PI.QnHermHaar.chatAa
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T16:08:06.566247+00:00
-- url     : https://prove2.me/theorems/a5a9f096-1f7c-405a-94bb-7b13cfceee40
-- title:
--   Qn Herm Haar: chat Aa
-- statement:
--   The Qn Herm Haar construction uses the chat Aa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/GeneralSecondMinorExpansion.lean#L18-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/GeneralSecondMinorExpansion.lean#L18-L24

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

theorem PI.QnHermHaar.chatAa {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (w : ℂ) (β : Fin m → ℂ)
    (p : Fin m) : chatA E w (Pi.single p 1) β =
      ∑ i : Fin m, ((-1 : ℂ) ^ ((i : ℕ) + (p : ℕ)) * β i) • qminor E (skip1 i) (skip1 p) w := by sorry
