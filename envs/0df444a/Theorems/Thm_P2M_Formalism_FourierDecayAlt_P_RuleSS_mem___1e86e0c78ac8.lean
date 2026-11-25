-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_RuleSS_mem___1e86e0c78ac8
-- name    : P2M_Formalism_FourierDecayAlt_P_RuleSS_mem___1e86e0c78ac8
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:55:36.225232+00:00
-- url     : https://prove2.me/theorems/3ff3d1f8-0ea4-4ac4-bc39-eb0d3bd59493
-- title:
--   P2 M Formalism Fourier Decay Alt P Rule SS mem   1e86e0c78ac8: P2 M Formalism Fourier Decay Alt P Rule SS mem   1e86e0c78ac8
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Rule SS mem   1e86e0c78ac8 construction uses the P2 M Formalism Fourier Decay Alt P Rule SS mem   1e86e0c78ac8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleSS.lean#L102-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleSS.lean#L102-L102

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

theorem P2M_Formalism_FourierDecayAlt_P_RuleSS_mem___1e86e0c78ac8 : L.ζ ∈ L.fns := by sorry

alias «Formalism».«FourierDecayAlt».«P».«RuleSS».«mem_ζ» := P2M_Formalism_FourierDecayAlt_P_RuleSS_mem___1e86e0c78ac8
