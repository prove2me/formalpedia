-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_LEx2_meas_th__13e6d05155eb
-- name    : P2M_Formalism_FourierDecayAlt_P_LEx2_meas_th__13e6d05155eb
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:55:50.243982+00:00
-- url     : https://prove2.me/theorems/43479a2f-7d28-4cb8-990c-14ad70f72768
-- title:
--   P2 M Formalism Fourier Decay Alt P LEx2 meas th  13e6d05155eb: P2 M Formalism Fourier Decay Alt P LEx2 meas th  13e6d05155eb
-- statement:
--   The P2 M Formalism Fourier Decay Alt P LEx2 meas th  13e6d05155eb construction uses the P2 M Formalism Fourier Decay Alt P LEx2 meas th  13e6d05155eb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedL2BoundedMul.lean#L337-L339
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedL2BoundedMul.lean#L337-L339

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeasIterDeriv
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaLimit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2BoundedMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate

theorem P2M_Formalism_FourierDecayAlt_P_LEx2_meas_th__13e6d05155eb (B : Base) (ε σ : ℝ) : Measurable fun ω => th ε σ (B.G ω) := by sorry

alias «Formalism».«FourierDecayAlt».«P».«LEx2».«meas_th'» := P2M_Formalism_FourierDecayAlt_P_LEx2_meas_th__13e6d05155eb
