-- Prove2me | Theorems.Thm_PI_QnHermHaar_commSumB
-- name    : PI.QnHermHaar.commSumB
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T15:50:07.463283+00:00
-- url     : https://prove2.me/theorems/622b1c6a-bad7-4a94-a200-3c44c1f2847a
-- title:
--   Qn Herm Haar: comm Sum B
-- statement:
--   The Qn Herm Haar construction uses the comm Sum B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/SumFourCommVersion.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/SumFourCommVersion.lean#L15-L17

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_LowerRightNeZeroOfUpperRightZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_SumFourCommVersion
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

theorem PI.QnHermHaar.commSumB {A : Type*} [Ring A] {ι : Type*} [Fintype ι] (h : ι → A) (g : A) :
    g * (∑ i, h i) - (∑ i, h i) * g = ∑ i, (g * h i - h i * g) := by sorry
