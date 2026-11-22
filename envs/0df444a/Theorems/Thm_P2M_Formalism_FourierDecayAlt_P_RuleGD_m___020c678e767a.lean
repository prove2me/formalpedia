-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_RuleGD_m___020c678e767a
-- name    : P2M_Formalism_FourierDecayAlt_P_RuleGD_m___020c678e767a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:13:51.186036+00:00
-- url     : https://prove2.me/theorems/af6b763b-a417-4256-8343-4edadcb5ce7f
-- title:
--   P2 M Formalism Fourier Decay Alt P Rule GD m   020c678e767a: P2 M Formalism Fourier Decay Alt P Rule GD m   020c678e767a
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Rule GD m   020c678e767a construction uses the P2 M Formalism Fourier Decay Alt P Rule GD m   020c678e767a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleGD.lean#L82-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleGD.lean#L82-L82

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleGD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RuleGD
open Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Matrix
variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}
variable (L : LevelData A r)

theorem P2M_Formalism_FourierDecayAlt_P_RuleGD_m___020c678e767a : L.ζ ∈ L.fns := by sorry

alias «Formalism».«FourierDecayAlt».«P».«RuleGD».«m_ζ» := P2M_Formalism_FourierDecayAlt_P_RuleGD_m___020c678e767a
