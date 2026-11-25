-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_NFx2_sb_mem___f35113da0eee
-- name    : P2M_Formalism_FourierDecayAlt_P_NFx2_sb_mem___f35113da0eee
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:56:17.31772+00:00
-- url     : https://prove2.me/theorems/4e1613d2-d7e0-43f3-b9d4-c5bf5e7485c3
-- title:
--   P2 M Formalism Fourier Decay Alt P NFx2 sb mem   f35113da0eee: P2 M Formalism Fourier Decay Alt P NFx2 sb mem   f35113da0eee
-- statement:
--   The P2 M Formalism Fourier Decay Alt P NFx2 sb mem   f35113da0eee construction uses the P2 M Formalism Fourier Decay Alt P NFx2 sb mem   f35113da0eee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L436-L436
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L436-L436

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

theorem P2M_Formalism_FourierDecayAlt_P_NFx2_sb_mem___f35113da0eee : L0.ζ ∈ L0.ops := by sorry

alias «Formalism».«FourierDecayAlt».«P».«NFx2».«sb_mem_ζ» := P2M_Formalism_FourierDecayAlt_P_NFx2_sb_mem___f35113da0eee
