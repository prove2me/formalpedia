-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_JFxE_hpart1_add__61ce7b77e173
-- name    : P2M_Formalism_FourierDecayAlt_P_JFxE_hpart1_add__61ce7b77e173
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:20:31.589492+00:00
-- url     : https://prove2.me/theorems/aa42d2e4-8e6b-41c4-9f89-9bdd400c5949
-- title:
--   P2 M Formalism Fourier Decay Alt P JFx E hpart1 add  61ce7b77e173: P2 M Formalism Fourier Decay Alt P JFx E hpart1 add  61ce7b77e173
-- statement:
--   The P2 M Formalism Fourier Decay Alt P JFx E hpart1 add  61ce7b77e173 construction uses the P2 M Formalism Fourier Decay Alt P JFx E hpart1 add  61ce7b77e173 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Hpart2EqZeroOfInLie.lean#L44-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Hpart2EqZeroOfInLie.lean#L44-L48

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BridgeQminor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Hpart2EqZeroOfInLie
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
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.JFxB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem P2M_Formalism_FourierDecayAlt_P_JFxE_hpart1_add__61ce7b77e173 (Z W : Mat k r) : hpart1 (Hpk k r) (Z + W) = hpart1 (Hpk k r) Z + hpart1 (Hpk k r) W := by sorry

alias «Formalism».«FourierDecayAlt».«P».«JFxE».«hpart1_add'» := P2M_Formalism_FourierDecayAlt_P_JFxE_hpart1_add__61ce7b77e173
