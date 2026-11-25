-- Prove2me | Theorems.Thm_PI_QnHermHaar_mulVecSingle
-- name    : PI.QnHermHaar.mulVecSingle
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T06:00:39.338426+00:00
-- url     : https://prove2.me/theorems/bdd50c58-a50b-44a6-b8d3-8e6d842496f1
-- title:
--   Qn Herm Haar: mul Vec Single
-- statement:
--   The Qn Herm Haar construction uses the mul Vec Single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/GeneralSecondMinorExpansion.lean#L65-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/GeneralSecondMinorExpansion.lean#L65-L70

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

theorem PI.QnHermHaar.mulVecSingle {m : ℕ} (Q : Matrix (Fin m) (Fin m) ℂ) (p p' : Fin m) :
    (Q *ᵥ Pi.single p (1 : ℂ)) p' = Q p' p := by sorry
