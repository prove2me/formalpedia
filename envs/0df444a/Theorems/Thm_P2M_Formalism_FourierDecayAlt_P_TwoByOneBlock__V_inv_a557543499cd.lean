-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_TwoByOneBlock__V_inv_a557543499cd
-- name    : P2M_Formalism_FourierDecayAlt_P_TwoByOneBlock__V_inv_a557543499cd
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T15:38:00.42192+00:00
-- url     : https://prove2.me/theorems/c70b0e4f-1cf7-48da-8953-36c70b33febf
-- title:
--   P2 M Formalism Fourier Decay Alt P Two By One Block  V inv a557543499cd: P2 M Formalism Fourier Decay Alt P Two By One Block  V inv a557543499cd
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Two By One Block  V inv a557543499cd construction uses the P2 M Formalism Fourier Decay Alt P Two By One Block  V inv a557543499cd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TwoByOneBlock.lean#L1348-L1354
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TwoByOneBlock.lean#L1348-L1354

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

theorem P2M_Formalism_FourierDecayAlt_P_TwoByOneBlock__V_inv_a557543499cd (T' : ℝ) {g : Mat k r} (hg : g ∈ UWb k r) : (σV k r T').map (fun v => g *ᵥ v) = σV k r T' := by sorry

alias «Formalism».«FourierDecayAlt».«P».«TwoByOneBlock».«σV_inv» := P2M_Formalism_FourierDecayAlt_P_TwoByOneBlock__V_inv_a557543499cd
