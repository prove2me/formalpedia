-- Prove2me | Theorems.Thm_PI_QnHermHaar_commSumA
-- name    : PI.QnHermHaar.commSumA
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T15:50:32.475945+00:00
-- url     : https://prove2.me/theorems/46db6eb5-bf3d-473a-b30c-8d6c78863b4b
-- title:
--   Qn Herm Haar: comm Sum A
-- statement:
--   The Qn Herm Haar construction uses the comm Sum A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/SumFourCommVersion.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/SumFourCommVersion.lean#L11-L13

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

theorem PI.QnHermHaar.commSumA {A : Type*} [Ring A] {ι : Type*} [Fintype ι] (h : ι → A) (g : A) :
    (∑ i, h i) * g - g * (∑ i, h i) = ∑ i, (h i * g - g * h i) := by sorry
