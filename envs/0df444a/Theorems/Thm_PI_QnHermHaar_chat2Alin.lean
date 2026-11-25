-- Prove2me | Theorems.Thm_PI_QnHermHaar_chat2Alin
-- name    : PI.QnHermHaar.chat2Alin
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T06:01:35.852987+00:00
-- url     : https://prove2.me/theorems/782f7321-e45b-439f-ace6-7a4ea8021db4
-- title:
--   Qn Herm Haar: chat2 Alin
-- statement:
--   The Qn Herm Haar construction uses the chat2 Alin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/GeneralSecondMinorExpansion.lean#L142-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/GeneralSecondMinorExpansion.lean#L142-L155

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

theorem PI.QnHermHaar.chat2Alin {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (w : ℂ)
    (a a' β β' : Fin m → ℂ) :
    chat2A E w a a' β β' = ∑ l, ∑ p, (β l * a p) • chat2A E w (Pi.single p 1) a' (Pi.single l 1) β' := by sorry
