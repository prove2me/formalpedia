-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_TwoByOneBlock__b_inv_582dedf997ff
-- name    : P2M_Formalism_FourierDecayAlt_P_TwoByOneBlock__b_inv_582dedf997ff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T15:37:17.744738+00:00
-- url     : https://prove2.me/theorems/c1c110b4-f23c-4e0f-a81f-3c648df76e2c
-- title:
--   P2 M Formalism Fourier Decay Alt P Two By One Block  b inv 582dedf997ff: P2 M Formalism Fourier Decay Alt P Two By One Block  b inv 582dedf997ff
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Two By One Block  b inv 582dedf997ff construction uses the P2 M Formalism Fourier Decay Alt P Two By One Block  b inv 582dedf997ff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TwoByOneBlock.lean#L1222-L1236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TwoByOneBlock.lean#L1222-L1236

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

theorem P2M_Formalism_FourierDecayAlt_P_TwoByOneBlock__b_inv_582dedf997ff (T' : ℝ) {μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hμ : μ ∈ UH (Hb k)) :
    (σb k T').map (fun u => μ *ᵥ u) = σb k T' := by sorry

alias «Formalism».«FourierDecayAlt».«P».«TwoByOneBlock».«σb_inv» := P2M_Formalism_FourierDecayAlt_P_TwoByOneBlock__b_inv_582dedf997ff
