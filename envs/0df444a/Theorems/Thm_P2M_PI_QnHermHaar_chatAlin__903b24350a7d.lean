-- Prove2me | Theorems.Thm_P2M_PI_QnHermHaar_chatAlin__903b24350a7d
-- name    : P2M_PI_QnHermHaar_chatAlin__903b24350a7d
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:57:51.637868+00:00
-- url     : https://prove2.me/theorems/87656306-a796-4017-b947-ac2abff53a13
-- title:
--   P2 M PI Qn Herm Haar chat Alin  903b24350a7d: P2 M PI Qn Herm Haar chat Alin  903b24350a7d
-- statement:
--   The P2 M PI Qn Herm Haar chat Alin  903b24350a7d construction uses the P2 M PI Qn Herm Haar chat Alin  903b24350a7d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/GeneralSecondMinorExpansion.lean#L41-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/GeneralSecondMinorExpansion.lean#L41-L47

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

theorem P2M_PI_QnHermHaar_chatAlin__903b24350a7d {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (w : ℂ)
    (a β : Fin m → ℂ) : chatA E w a β = ∑ l, β l • chatA E w a (Pi.single l 1) := by sorry

alias «PI».«QnHermHaar».«chatAlinβ» := P2M_PI_QnHermHaar_chatAlin__903b24350a7d
