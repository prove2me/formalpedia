-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_RuleGD_m__b_202003117e66
-- name    : P2M_Formalism_FourierDecayAlt_P_RuleGD_m__b_202003117e66
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:13:57.912002+00:00
-- url     : https://prove2.me/theorems/98ca26e4-8495-4283-b955-b0510b020c40
-- title:
--   P2 M Formalism Fourier Decay Alt P Rule GD m  b 202003117e66: P2 M Formalism Fourier Decay Alt P Rule GD m  b 202003117e66
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Rule GD m  b 202003117e66 construction uses the P2 M Formalism Fourier Decay Alt P Rule GD m  b 202003117e66 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleGD.lean#L84-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleGD.lean#L84-L84

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

theorem P2M_Formalism_FourierDecayAlt_P_RuleGD_m__b_202003117e66 : L.ζb ∈ L.fns := by sorry

alias «Formalism».«FourierDecayAlt».«P».«RuleGD».«m_ζb» := P2M_Formalism_FourierDecayAlt_P_RuleGD_m__b_202003117e66
