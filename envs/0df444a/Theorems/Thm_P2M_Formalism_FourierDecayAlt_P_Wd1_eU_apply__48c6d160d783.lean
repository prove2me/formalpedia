-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Wd1_eU_apply__48c6d160d783
-- name    : P2M_Formalism_FourierDecayAlt_P_Wd1_eU_apply__48c6d160d783
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:55:30.793077+00:00
-- url     : https://prove2.me/theorems/99ffe0ac-936e-4a1d-acca-ae2b740ba0f4
-- title:
--   P2 M Formalism Fourier Decay Alt P Wd1 e U apply  48c6d160d783: P2 M Formalism Fourier Decay Alt P Wd1 e U apply  48c6d160d783
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Wd1 e U apply  48c6d160d783 construction uses the P2 M Formalism Fourier Decay Alt P Wd1 e U apply  48c6d160d783 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PositionInsertionDiagonalCompat.lean#L38-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PositionInsertionDiagonalCompat.lean#L38-L41

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

theorem P2M_Formalism_FourierDecayAlt_P_Wd1_eU_apply__48c6d160d783 (a : S) (i j : Fin 2) (x y : Ix S) :
    (eU a i j : SlopeTestRemainingChoices S A) x y = if y a = j ∧ x = Function.update y a i then 1 else 0 := by sorry

alias «Formalism».«FourierDecayAlt».«P».«Wd1».«eU_apply'» := P2M_Formalism_FourierDecayAlt_P_Wd1_eU_apply__48c6d160d783
