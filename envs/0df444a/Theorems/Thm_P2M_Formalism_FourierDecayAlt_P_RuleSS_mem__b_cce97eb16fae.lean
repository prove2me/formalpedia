-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_RuleSS_mem__b_cce97eb16fae
-- name    : P2M_Formalism_FourierDecayAlt_P_RuleSS_mem__b_cce97eb16fae
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:55:34.456506+00:00
-- url     : https://prove2.me/theorems/4815a8ff-280a-4ccc-a499-a504b97ea97f
-- title:
--   P2 M Formalism Fourier Decay Alt P Rule SS mem  b cce97eb16fae: P2 M Formalism Fourier Decay Alt P Rule SS mem  b cce97eb16fae
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Rule SS mem  b cce97eb16fae construction uses the P2 M Formalism Fourier Decay Alt P Rule SS mem  b cce97eb16fae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleSS.lean#L103-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleSS.lean#L103-L103

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleSS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RuleSS
open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData
variable {A : Type} [Ring A] [Algebra ℂ A]
variable {r : ℕ} (L : LevelData A r)

theorem P2M_Formalism_FourierDecayAlt_P_RuleSS_mem__b_cce97eb16fae : L.ζb ∈ L.fns := by sorry

alias «Formalism».«FourierDecayAlt».«P».«RuleSS».«mem_ζb» := P2M_Formalism_FourierDecayAlt_P_RuleSS_mem__b_cce97eb16fae
