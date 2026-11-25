-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_LongWeylElement_fin_cases__0856e4f673a2
-- name    : P2M_Formalism_FourierDecayAlt_P_LongWeylElement_fin_cases__0856e4f673a2
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:56:06.865494+00:00
-- url     : https://prove2.me/theorems/36d7e86a-2067-4e0f-a9a8-8b62df395a4b
-- title:
--   P2 M Formalism Fourier Decay Alt P Long Weyl Element fin cases  0856e4f673a2: P2 M Formalism Fourier Decay Alt P Long Weyl Element fin cases  0856e4f673a2
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Long Weyl Element fin cases  0856e4f673a2 construction uses the P2 M Formalism Fourier Decay Alt P Long Weyl Element fin cases  0856e4f673a2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LongWeylElement.lean#L370-L378
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LongWeylElement.lean#L370-L378

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
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
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LongWeylElement
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}

theorem P2M_Formalism_FourierDecayAlt_P_LongWeylElement_fin_cases__0856e4f673a2 (a : Fin (1 + r')) : a = a0 r' ∨ ∃ a' : Fin r', a = Fin.natAdd 1 a' := by sorry

alias «Formalism».«FourierDecayAlt».«P».«LongWeylElement».«fin_cases'» := P2M_Formalism_FourierDecayAlt_P_LongWeylElement_fin_cases__0856e4f673a2
