-- Prove2me | Theorems.Thm_PI_QnHermHaar_sumSingle
-- name    : PI.QnHermHaar.sumSingle
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:37:17.9264+00:00
-- url     : https://prove2.me/theorems/56c35d94-9049-4998-8c3d-6155c9dc01c4
-- title:
--   Qn Herm Haar: sum Single
-- statement:
--   The Qn Herm Haar construction uses the sum Single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/GeneralSecondMinorExpansion.lean#L90-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/GeneralSecondMinorExpansion.lean#L90-L94

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

theorem PI.QnHermHaar.sumSingle {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (W : Fin m → A) (c : Fin m → ℂ) (i i' : Fin m) :
    W i * algebraMap ℂ A (c i') - W i' * algebraMap ℂ A (c i) =
      ∑ l, ((Pi.single l (1 : ℂ) : Fin m → ℂ) i * c i' - (Pi.single l (1 : ℂ) : Fin m → ℂ) i' * c i) • W l := by sorry
