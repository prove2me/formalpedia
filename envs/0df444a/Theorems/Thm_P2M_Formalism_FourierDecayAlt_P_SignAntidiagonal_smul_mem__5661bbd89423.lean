-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_SignAntidiagonal_smul_mem__5661bbd89423
-- name    : P2M_Formalism_FourierDecayAlt_P_SignAntidiagonal_smul_mem__5661bbd89423
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:15:16.842403+00:00
-- url     : https://prove2.me/theorems/ae09dc1d-e8ef-4736-8f5b-f9e6a58f84b1
-- title:
--   P2 M Formalism Fourier Decay Alt P Sign Antidiagonal smul mem  5661bbd89423: P2 M Formalism Fourier Decay Alt P Sign Antidiagonal smul mem  5661bbd89423
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Sign Antidiagonal smul mem  5661bbd89423 construction uses the P2 M Formalism Fourier Decay Alt P Sign Antidiagonal smul mem  5661bbd89423 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstPeelingMinorMemIdeal.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstPeelingMinorMemIdeal.lean#L18-L20

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThirdPolynomialExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstPeelingMinorMemIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants
variable {A : Type} [Ring A] [Algebra ℂ A]

theorem P2M_Formalism_FourierDecayAlt_P_SignAntidiagonal_smul_mem__5661bbd89423 (I : Ideal A) (c : ℂ) {x : A} (hx : x ∈ I) : c • x ∈ I := by sorry

alias «Formalism».«FourierDecayAlt».«P».«SignAntidiagonal».«smul_mem'» := P2M_Formalism_FourierDecayAlt_P_SignAntidiagonal_smul_mem__5661bbd89423
