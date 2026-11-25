-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Wd1_cond_iff__300993909eb5
-- name    : P2M_Formalism_FourierDecayAlt_P_Wd1_cond_iff__300993909eb5
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:55:31.236839+00:00
-- url     : https://prove2.me/theorems/7ac986a2-1522-4ea3-9b63-a7ae06601c35
-- title:
--   P2 M Formalism Fourier Decay Alt P Wd1 cond iff  300993909eb5: P2 M Formalism Fourier Decay Alt P Wd1 cond iff  300993909eb5
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Wd1 cond iff  300993909eb5 construction uses the P2 M Formalism Fourier Decay Alt P Wd1 cond iff  300993909eb5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PositionInsertionDiagonalCompat.lean#L21-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PositionInsertionDiagonalCompat.lean#L21-L31

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd1
open Matrix Formalism.FourierDecayAlt.Wd
variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]

theorem P2M_Formalism_FourierDecayAlt_P_Wd1_cond_iff__300993909eb5 (a : S) (i j : Fin 2) (x y : Ix S) :
    (x a = i ∧ y a = j ∧ ∀ b, b ≠ a → x b = y b) ↔ (y a = j ∧ x = Function.update y a i) := by sorry

alias «Formalism».«FourierDecayAlt».«P».«Wd1».«cond_iff'» := P2M_Formalism_FourierDecayAlt_P_Wd1_cond_iff__300993909eb5
