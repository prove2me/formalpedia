-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_R_LevelData_inv_mem___78c8e7adc78b
-- name    : P2M_Formalism_FourierDecayAlt_R_LevelData_inv_mem___78c8e7adc78b
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:55:37.91572+00:00
-- url     : https://prove2.me/theorems/eca8e8bd-4d09-42b8-8e06-cda12eb13180
-- title:
--   P2 M Formalism Fourier Decay Alt R Level Data inv mem   78c8e7adc78b: P2 M Formalism Fourier Decay Alt R Level Data inv mem   78c8e7adc78b
-- statement:
--   The P2 M Formalism Fourier Decay Alt R Level Data inv mem   78c8e7adc78b construction uses the P2 M Formalism Fourier Decay Alt R Level Data inv mem   78c8e7adc78b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleInv.lean#L49-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleInv.lean#L49-L49

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

theorem P2M_Formalism_FourierDecayAlt_R_LevelData_inv_mem___78c8e7adc78b : L.ζ ∈ L.fns := by sorry

alias «Formalism».«FourierDecayAlt».«R».«LevelData».«inv_mem_ζ» := P2M_Formalism_FourierDecayAlt_R_LevelData_inv_mem___78c8e7adc78b
