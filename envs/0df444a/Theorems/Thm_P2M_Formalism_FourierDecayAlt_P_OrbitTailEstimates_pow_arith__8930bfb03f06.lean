-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_OrbitTailEstimates_pow_arith__8930bfb03f06
-- name    : P2M_Formalism_FourierDecayAlt_P_OrbitTailEstimates_pow_arith__8930bfb03f06
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:55:57.423804+00:00
-- url     : https://prove2.me/theorems/b4fe775a-63eb-4f34-be03-0f41403427d6
-- title:
--   P2 M Formalism Fourier Decay Alt P Orbit Tail Estimates pow arith  8930bfb03f06: P2 M Formalism Fourier Decay Alt P Orbit Tail Estimates pow arith  8930bfb03f06
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Orbit Tail Estimates pow arith  8930bfb03f06 construction uses the P2 M Formalism Fourier Decay Alt P Orbit Tail Estimates pow arith  8930bfb03f06 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitTailEstimates.lean#L300-L306
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitTailEstimates.lean#L300-L306

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitTailEstimates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrbitTailEstimates
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2 Formalism.FourierDecayAlt.P.G7

theorem P2M_Formalism_FourierDecayAlt_P_OrbitTailEstimates_pow_arith__8930bfb03f06 (m : ℕ) (x : ℝ) (hx : 0 < x) :
    x ^ ((m + 1) ^ 2) * (x ^ ((m + 1) * (m + 4)))⁻¹ = x * (x ^ (3 * m + 4))⁻¹ := by sorry

alias «Formalism».«FourierDecayAlt».«P».«OrbitTailEstimates».«pow_arith'» := P2M_Formalism_FourierDecayAlt_P_OrbitTailEstimates_pow_arith__8930bfb03f06
