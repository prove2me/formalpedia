-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_TwoByOneBlock__b_conc_b7269f632f6d
-- name    : P2M_Formalism_FourierDecayAlt_P_TwoByOneBlock__b_conc_b7269f632f6d
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:56:02.739733+00:00
-- url     : https://prove2.me/theorems/733eaa97-ae46-49f1-b090-1951850ea30d
-- title:
--   P2 M Formalism Fourier Decay Alt P Two By One Block  b conc b7269f632f6d: P2 M Formalism Fourier Decay Alt P Two By One Block  b conc b7269f632f6d
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Two By One Block  b conc b7269f632f6d construction uses the P2 M Formalism Fourier Decay Alt P Two By One Block  b conc b7269f632f6d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TwoByOneBlock.lean#L1238-L1244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TwoByOneBlock.lean#L1238-L1244

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

theorem P2M_Formalism_FourierDecayAlt_P_TwoByOneBlock__b_conc_b7269f632f6d {T' : ℝ} (hT' : 0 < T') : ∀ᵐ u ∂σb k T', Nq k u = T' := by sorry

alias «Formalism».«FourierDecayAlt».«P».«TwoByOneBlock».«σb_conc» := P2M_Formalism_FourierDecayAlt_P_TwoByOneBlock__b_conc_b7269f632f6d
