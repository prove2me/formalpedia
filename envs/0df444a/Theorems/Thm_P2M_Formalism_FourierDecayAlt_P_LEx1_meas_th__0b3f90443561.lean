-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_LEx1_meas_th__0b3f90443561
-- name    : P2M_Formalism_FourierDecayAlt_P_LEx1_meas_th__0b3f90443561
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:04:50.68902+00:00
-- url     : https://prove2.me/theorems/161404fe-c122-58ec-9a36-94e3f903b3e6
-- title:
--   P2 M Formalism Fourier Decay Alt P LEx1 meas th  0b3f90443561: P2 M Formalism Fourier Decay Alt P LEx1 meas th  0b3f90443561
-- statement:
--   The P2 M Formalism Fourier Decay Alt P LEx1 meas th  0b3f90443561 construction uses the P2 M Formalism Fourier Decay Alt P LEx1 meas th  0b3f90443561 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedL2ConstMul.lean#L300-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedL2ConstMul.lean#L300-L300

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StepClaimFromStepsFull
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2ConstMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate

theorem P2M_Formalism_FourierDecayAlt_P_LEx1_meas_th__0b3f90443561 (B : Base) (ε σ : ℝ) : Measurable fun ω => th ε σ (B.G ω) := by sorry

alias «Formalism».«FourierDecayAlt».«P».«LEx1».«meas_th'» := P2M_Formalism_FourierDecayAlt_P_LEx1_meas_th__0b3f90443561
