-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_FourTermExpansion_top_apply___a095e6ea583d
-- name    : P2M_Formalism_FourierDecayAlt_P_FourTermExpansion_top_apply___a095e6ea583d
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:03:59.298798+00:00
-- url     : https://prove2.me/theorems/3cf06c1f-bf1d-42fd-9cb3-0b2fd7c39a42
-- title:
--   P2 M Formalism Fourier Decay Alt P Four Term Expansion top apply   a095e6ea583d: P2 M Formalism Fourier Decay Alt P Four Term Expansion top apply   a095e6ea583d
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Four Term Expansion top apply   a095e6ea583d construction uses the P2 M Formalism Fourier Decay Alt P Four Term Expansion top apply   a095e6ea583d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FourTermExpansion.lean#L59-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FourTermExpansion.lean#L59-L60

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourTermExpansion
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FourTermExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (M : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Mat k r)

theorem P2M_Formalism_FourierDecayAlt_P_FourTermExpansion_top_apply___a095e6ea583d (v : ℂ) (a b : Fin (2 * r + k + 1)) (Φ : Mat k r → E) (g : Mat k r) :
    Top (LT M) v a b Φ g = (if a = b then v • Φ g else 0) + EZ (M a b) Φ g := by sorry

alias «Formalism».«FourierDecayAlt».«P».«FourTermExpansion».«top_apply''» := P2M_Formalism_FourierDecayAlt_P_FourTermExpansion_top_apply___a095e6ea583d
