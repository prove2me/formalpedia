-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_NFx2_sb_GGi__b_1df21f612a80
-- name    : P2M_Formalism_FourierDecayAlt_P_NFx2_sb_GGi__b_1df21f612a80
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:58:15.282521+00:00
-- url     : https://prove2.me/theorems/a8071e82-5a8e-409c-a29b-49280146a694
-- title:
--   P2 M Formalism Fourier Decay Alt P NFx2 sb GGi  b 1df21f612a80: P2 M Formalism Fourier Decay Alt P NFx2 sb GGi  b 1df21f612a80
-- statement:
--   The P2 M Formalism Fourier Decay Alt P NFx2 sb GGi  b 1df21f612a80 construction uses the P2 M Formalism Fourier Decay Alt P NFx2 sb GGi  b 1df21f612a80 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L454-L455
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L454-L455

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
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {L0 : PreLevel A P.r}
  {QQ : ℂ → Matrix (Fin 2) (Fin 2) A} {κ : (M.Ty P → ℂ) →ₐ[ℂ] A}

theorem P2M_Formalism_FourierDecayAlt_P_NFx2_sb_GGi__b_1df21f612a80 : L0.GGi * L0.ζb = L0.ζb * L0.GGi := by sorry

alias «Formalism».«FourierDecayAlt».«P».«NFx2».«sb_GGi_ζb» := P2M_Formalism_FourierDecayAlt_P_NFx2_sb_GGi__b_1df21f612a80
