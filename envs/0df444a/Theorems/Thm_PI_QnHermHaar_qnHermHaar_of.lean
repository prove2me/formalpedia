-- Prove2me | Theorems.Thm_PI_QnHermHaar_qnHermHaar_of
-- name    : PI.QnHermHaar.qnHermHaar_of
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T06:01:09.916651+00:00
-- url     : https://prove2.me/theorems/277cda41-c248-4aa8-8392-d8f3cb2fea68
-- title:
--   Qn Herm Haar: qn Herm Haar of
-- statement:
--   The Qn Herm Haar construction uses the qn Herm Haar of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/Development.lean#L93-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/Development.lean#L93-L96

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_Development
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset MeasureTheory
noncomputable section
open PI PI.QnHermHaar
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem PI.QnHermHaar.qnHermHaar_of (hA : HermAlgFrom) (hE : EabAdjFrom) (hT : EabTest) (hM : MulTest) (hI : TestInt)
    (hY : YbRel) (hX : XbRel) (hH : HmFacts) (hG : Glue) :
    RdSkew → StarMinor → ContractionsCovariant → MoveVec → MoveCov → YLeibniz → EabGlLev → EabPres → HermHaar := by sorry
