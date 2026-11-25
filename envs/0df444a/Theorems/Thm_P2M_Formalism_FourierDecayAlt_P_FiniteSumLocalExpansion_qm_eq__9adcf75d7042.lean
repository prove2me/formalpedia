-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_FiniteSumLocalExpansion_qm_eq__9adcf75d7042
-- name    : P2M_Formalism_FourierDecayAlt_P_FiniteSumLocalExpansion_qm_eq__9adcf75d7042
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:57:03.966663+00:00
-- url     : https://prove2.me/theorems/8df7814f-d01f-42bf-b94a-533c8bd0d7ca
-- title:
--   P2 M Formalism Fourier Decay Alt P Finite Sum Local Expansion qm eq  9adcf75d7042: P2 M Formalism Fourier Decay Alt P Finite Sum Local Expansion qm eq  9adcf75d7042
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Finite Sum Local Expansion qm eq  9adcf75d7042 construction uses the P2 M Formalism Fourier Decay Alt P Finite Sum Local Expansion qm eq  9adcf75d7042 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FiniteSumLocalExpansion.lean#L210-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FiniteSumLocalExpansion.lean#L210-L219

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourTermExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfCVUnderIntOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellOrbitSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FiniteSumLocalExpansion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
  Formalism.FourierDecayAlt.P.FourTermExpansion
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem P2M_Formalism_FourierDecayAlt_P_FiniteSumLocalExpansion_qm_eq__9adcf75d7042 (M : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Mat k r) {t : ℕ}
    (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) (Φ : Mat k r → E) (g : Mat k r) :
    qminorOp (FourTermExpansion.LT M) a b u Φ g = ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      fold M (List.ofFn fun j : Fin t => (u - ((j : ℕ) : ℂ), a (σ j), b j)) Φ g := by sorry

alias «Formalism».«FourierDecayAlt».«P».«FiniteSumLocalExpansion».«qm_eq'» := P2M_Formalism_FourierDecayAlt_P_FiniteSumLocalExpansion_qm_eq__9adcf75d7042
