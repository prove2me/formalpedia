-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B2x8__t_meas_3efb4587c898
-- name    : P2M_Formalism_FourierDecayAlt_P_B2x8__t_meas_3efb4587c898
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T15:00:36.35582+00:00
-- url     : https://prove2.me/theorems/cbc7414b-1ff0-4133-8407-5d8083f6a489
-- title:
--   P2 M Formalism Fourier Decay Alt P B2x8  t meas 3efb4587c898: P2 M Formalism Fourier Decay Alt P B2x8  t meas 3efb4587c898
-- statement:
--   The P2 M Formalism Fourier Decay Alt P B2x8  t meas 3efb4587c898 construction uses the P2 M Formalism Fourier Decay Alt P B2x8  t meas 3efb4587c898 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L637-L643
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L637-L643

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}

theorem P2M_Formalism_FourierDecayAlt_P_B2x8__t_meas_3efb4587c898 : Measurable (Ψt k r') := by sorry

alias «Formalism».«FourierDecayAlt».«P».«B2x8».«Ψt_meas» := P2M_Formalism_FourierDecayAlt_P_B2x8__t_meas_3efb4587c898
