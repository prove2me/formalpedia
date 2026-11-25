-- Prove2me | Theorems.Thm_PI_QnHermHaar_vecMulSingle
-- name    : PI.QnHermHaar.vecMulSingle
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:21:56.334673+00:00
-- url     : https://prove2.me/theorems/f711112b-2a4c-4bfa-8686-fcd32327cee4
-- title:
--   Qn Herm Haar: vec Mul Single
-- statement:
--   The Qn Herm Haar construction uses the vec Mul Single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/GeneralSecondMinorExpansion.lean#L58-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/GeneralSecondMinorExpansion.lean#L58-L63

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

theorem PI.QnHermHaar.vecMulSingle {m : ℕ} (P : Matrix (Fin m) (Fin m) ℂ) (l l' : Fin m) :
    (Pi.single l (1 : ℂ) ᵥ* P) l' = P l l' := by sorry
