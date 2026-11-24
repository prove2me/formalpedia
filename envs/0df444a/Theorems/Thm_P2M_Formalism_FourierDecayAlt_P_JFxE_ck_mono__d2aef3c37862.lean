-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_JFxE_ck_mono__d2aef3c37862
-- name    : P2M_Formalism_FourierDecayAlt_P_JFxE_ck_mono__d2aef3c37862
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:27:34.920807+00:00
-- url     : https://prove2.me/theorems/28f21857-dd5d-4da0-8e90-da3839844bfc
-- title:
--   P2 M Formalism Fourier Decay Alt P JFx E ck mono  d2aef3c37862: P2 M Formalism Fourier Decay Alt P JFx E ck mono  d2aef3c37862
-- statement:
--   The P2 M Formalism Fourier Decay Alt P JFx E ck mono  d2aef3c37862 construction uses the P2 M Formalism Fourier Decay Alt P JFx E ck mono  d2aef3c37862 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RepIntCastMul.lean#L152-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RepIntCastMul.lean#L152-L157

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DetRowsZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RepIntCastMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxE
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))

theorem P2M_Formalism_FourierDecayAlt_P_JFxE_ck_mono__d2aef3c37862 {m m' : ℕ} (h : m ≤ m') {f : Mat k r → E} (hf : CkOn ((m' : ℕ) : ℕ∞) (GV k r) f) :
    CkOn ((m : ℕ) : ℕ∞) (GV k r) f := by sorry

alias «Formalism».«FourierDecayAlt».«P».«JFxE».«ck_mono'» := P2M_Formalism_FourierDecayAlt_P_JFxE_ck_mono__d2aef3c37862
