-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_R_LevelData_inv_mem__b_d9e4f796149b
-- name    : P2M_Formalism_FourierDecayAlt_R_LevelData_inv_mem__b_d9e4f796149b
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:55:52.932822+00:00
-- url     : https://prove2.me/theorems/737f27cb-2b6a-4bdb-b058-5772dd32d9aa
-- title:
--   P2 M Formalism Fourier Decay Alt R Level Data inv mem  b d9e4f796149b: P2 M Formalism Fourier Decay Alt R Level Data inv mem  b d9e4f796149b
-- statement:
--   The P2 M Formalism Fourier Decay Alt R Level Data inv mem  b d9e4f796149b construction uses the P2 M Formalism Fourier Decay Alt R Level Data inv mem  b d9e4f796149b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleInv.lean#L51-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleInv.lean#L51-L51

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.PInv
open Matrix LevelData
variable {A : Type} [Ring A] [Algebra ℂ A]
variable {r : ℕ} (L : LevelData A r)

theorem P2M_Formalism_FourierDecayAlt_R_LevelData_inv_mem__b_d9e4f796149b : L.ζb ∈ L.fns := by sorry

alias «Formalism».«FourierDecayAlt».«R».«LevelData».«inv_mem_ζb» := P2M_Formalism_FourierDecayAlt_R_LevelData_inv_mem__b_d9e4f796149b
