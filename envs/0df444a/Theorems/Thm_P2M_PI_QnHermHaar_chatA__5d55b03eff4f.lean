-- Prove2me | Theorems.Thm_P2M_PI_QnHermHaar_chatA__5d55b03eff4f
-- name    : P2M_PI_QnHermHaar_chatA__5d55b03eff4f
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:08:44.784844+00:00
-- url     : https://prove2.me/theorems/28323382-a061-4a73-9653-c00f9f4a0751
-- title:
--   P2 M PI Qn Herm Haar chat A  5d55b03eff4f: P2 M PI Qn Herm Haar chat A  5d55b03eff4f
-- statement:
--   The P2 M PI Qn Herm Haar chat A  5d55b03eff4f construction uses the P2 M PI Qn Herm Haar chat A  5d55b03eff4f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/GeneralSecondMinorExpansion.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/GeneralSecondMinorExpansion.lean#L11-L16

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

theorem P2M_PI_QnHermHaar_chatA__5d55b03eff4f {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (w : ℂ) (a : Fin m → ℂ)
    (l : Fin m) : chatA E w a (Pi.single l 1) =
      ∑ j : Fin m, ((-1 : ℂ) ^ ((l : ℕ) + (j : ℕ)) * a j) • qminor E (skip1 l) (skip1 j) w := by sorry

alias «PI».«QnHermHaar».«chatAβ» := P2M_PI_QnHermHaar_chatA__5d55b03eff4f
