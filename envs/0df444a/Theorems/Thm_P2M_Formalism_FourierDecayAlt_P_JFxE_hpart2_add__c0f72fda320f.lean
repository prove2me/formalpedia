-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_JFxE_hpart2_add__c0f72fda320f
-- name    : P2M_Formalism_FourierDecayAlt_P_JFxE_hpart2_add__c0f72fda320f
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:35:56.345202+00:00
-- url     : https://prove2.me/theorems/9fd83e21-587e-45cc-b7e7-a4d69c865e31
-- title:
--   P2 M Formalism Fourier Decay Alt P JFx E hpart2 add  c0f72fda320f: P2 M Formalism Fourier Decay Alt P JFx E hpart2 add  c0f72fda320f
-- statement:
--   The P2 M Formalism Fourier Decay Alt P JFx E hpart2 add  c0f72fda320f construction uses the P2 M Formalism Fourier Decay Alt P JFx E hpart2 add  c0f72fda320f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Hpart2EqZeroOfInLie.lean#L50-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Hpart2EqZeroOfInLie.lean#L50-L54

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

theorem P2M_Formalism_FourierDecayAlt_P_JFxE_hpart2_add__c0f72fda320f (Z W : Mat k r) : hpart2 (Hpk k r) (Z + W) = hpart2 (Hpk k r) Z + hpart2 (Hpk k r) W := by sorry

alias «Formalism».«FourierDecayAlt».«P».«JFxE».«hpart2_add'» := P2M_Formalism_FourierDecayAlt_P_JFxE_hpart2_add__c0f72fda320f
