-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_NFx2_sc_GG_GGi_958e5f9477be
-- name    : P2M_Formalism_FourierDecayAlt_P_NFx2_sc_GG_GGi_958e5f9477be
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T15:38:17.62267+00:00
-- url     : https://prove2.me/theorems/453d8151-613c-4280-a278-5bcc8cb27222
-- title:
--   P2 M Formalism Fourier Decay Alt P NFx2 sc GG GGi 958e5f9477be: P2 M Formalism Fourier Decay Alt P NFx2 sc GG GGi 958e5f9477be
-- statement:
--   The P2 M Formalism Fourier Decay Alt P NFx2 sc GG GGi 958e5f9477be construction uses the P2 M Formalism Fourier Decay Alt P NFx2 sc GG GGi 958e5f9477be property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L2038-L2039
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L2038-L2039

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Polynomial
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFx2
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.NF
noncomputable section
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]
variable {L0 : PreLevel A P.r} {QQ : ℂ → Matrix (Fin 2) (Fin 2) A} {κ : (M.Ty P → ℂ) →ₐ[ℂ] A}
  {b : M.Ty P → A} {SS : ℕ → A}

theorem P2M_Formalism_FourierDecayAlt_P_NFx2_sc_GG_GGi_958e5f9477be (L0 : PreLevel A P.r) : L0.GG * (L0.ζ * L0.GGi) = L0.ζ := by sorry

alias «Formalism».«FourierDecayAlt».«P».«NFx2».«sc_GGζGGi» := P2M_Formalism_FourierDecayAlt_P_NFx2_sc_GG_GGi_958e5f9477be
