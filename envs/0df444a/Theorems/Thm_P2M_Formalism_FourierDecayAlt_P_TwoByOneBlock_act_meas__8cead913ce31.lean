-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_TwoByOneBlock_act_meas__8cead913ce31
-- name    : P2M_Formalism_FourierDecayAlt_P_TwoByOneBlock_act_meas__8cead913ce31
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T15:38:31.587245+00:00
-- url     : https://prove2.me/theorems/092608dc-cad5-4efb-8129-d81bf4b659bc
-- title:
--   P2 M Formalism Fourier Decay Alt P Two By One Block act meas  8cead913ce31: P2 M Formalism Fourier Decay Alt P Two By One Block act meas  8cead913ce31
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Two By One Block act meas  8cead913ce31 construction uses the P2 M Formalism Fourier Decay Alt P Two By One Block act meas  8cead913ce31 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TwoByOneBlock.lean#L1318-L1323
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TwoByOneBlock.lean#L1318-L1323

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

theorem P2M_Formalism_FourierDecayAlt_P_TwoByOneBlock_act_meas__8cead913ce31 : Measurable (fun p : (Fin (2 * r + k + 1) → ℂ) × Mt k r => act p.2 p.1) := by sorry

alias «Formalism».«FourierDecayAlt».«P».«TwoByOneBlock».«act_meas'» := P2M_Formalism_FourierDecayAlt_P_TwoByOneBlock_act_meas__8cead913ce31
