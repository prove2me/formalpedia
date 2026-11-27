-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_NFx2_sb_GG__b_f5e5cf4e3bdf
-- name    : P2M_Formalism_FourierDecayAlt_P_NFx2_sb_GG__b_f5e5cf4e3bdf
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:10:48.221749+00:00
-- url     : https://prove2.me/theorems/5a392691-cb83-5c91-8978-85649ce5f199
-- title:
--   P2 M Formalism Fourier Decay Alt P NFx2 sb GG  b f5e5cf4e3bdf: P2 M Formalism Fourier Decay Alt P NFx2 sb GG  b f5e5cf4e3bdf
-- statement:
--   The P2 M Formalism Fourier Decay Alt P NFx2 sb GG  b f5e5cf4e3bdf construction uses the P2 M Formalism Fourier Decay Alt P NFx2 sb GG  b f5e5cf4e3bdf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L451-L452
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L451-L452

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

theorem P2M_Formalism_FourierDecayAlt_P_NFx2_sb_GG__b_f5e5cf4e3bdf : L0.GG * L0.ζb = L0.ζb * L0.GG := by sorry

alias «Formalism».«FourierDecayAlt».«P».«NFx2».«sb_GG_ζb» := P2M_Formalism_FourierDecayAlt_P_NFx2_sb_GG__b_f5e5cf4e3bdf
