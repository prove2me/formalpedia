-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_R_LevelData_inv_mem__i_46b19cb3119f
-- name    : P2M_Formalism_FourierDecayAlt_R_LevelData_inv_mem__i_46b19cb3119f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:04:09.848723+00:00
-- url     : https://prove2.me/theorems/e4a97a21-bb05-48b2-b4dd-34b6b360a0f2
-- title:
--   P2 M Formalism Fourier Decay Alt R Level Data inv mem  i 46b19cb3119f: P2 M Formalism Fourier Decay Alt R Level Data inv mem  i 46b19cb3119f
-- statement:
--   The P2 M Formalism Fourier Decay Alt R Level Data inv mem  i 46b19cb3119f construction uses the P2 M Formalism Fourier Decay Alt R Level Data inv mem  i 46b19cb3119f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleInv.lean#L50-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleInv.lean#L50-L50

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

theorem P2M_Formalism_FourierDecayAlt_R_LevelData_inv_mem__i_46b19cb3119f : L.ζi ∈ L.fns := by sorry

alias «Formalism».«FourierDecayAlt».«R».«LevelData».«inv_mem_ζi» := P2M_Formalism_FourierDecayAlt_R_LevelData_inv_mem__i_46b19cb3119f
