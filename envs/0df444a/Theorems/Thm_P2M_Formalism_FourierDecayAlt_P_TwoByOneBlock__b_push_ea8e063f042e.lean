-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_TwoByOneBlock__b_push_ea8e063f042e
-- name    : P2M_Formalism_FourierDecayAlt_P_TwoByOneBlock__b_push_ea8e063f042e
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:56:48.425027+00:00
-- url     : https://prove2.me/theorems/8f9985cd-2494-4c34-b976-e27e8e932c63
-- title:
--   P2 M Formalism Fourier Decay Alt P Two By One Block  b push ea8e063f042e: P2 M Formalism Fourier Decay Alt P Two By One Block  b push ea8e063f042e
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Two By One Block  b push ea8e063f042e construction uses the P2 M Formalism Fourier Decay Alt P Two By One Block  b push ea8e063f042e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TwoByOneBlock.lean#L1252-L1285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TwoByOneBlock.lean#L1252-L1285

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TwoByOneBlock
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}

theorem P2M_Formalism_FourierDecayAlt_P_TwoByOneBlock__b_push_ea8e063f042e (hk : 1 ≤ k) {T T' : ℝ} (hT : 0 < T) (hT' : 0 < T') (zb : Fin (k + 1) → ℂ)
    (hz : herm (Hb k) zb zb = -((T : ℝ) : ℂ)) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ (σb k T').map (fun u => herm (Hb k) u zb) =
      c • (volume : Measure ℂ).withDensity (fun ζ => ENNReal.ofReal (zWeight k T T' ζ)) := by sorry

alias «Formalism».«FourierDecayAlt».«P».«TwoByOneBlock».«σb_push» := P2M_Formalism_FourierDecayAlt_P_TwoByOneBlock__b_push_ea8e063f042e
