-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Wd7_cond_iff__d5515724d8c4
-- name    : P2M_Formalism_FourierDecayAlt_P_Wd7_cond_iff__d5515724d8c4
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:55:29.15626+00:00
-- url     : https://prove2.me/theorems/35883b0f-49b0-44b2-99e7-46fe19b421c1
-- title:
--   P2 M Formalism Fourier Decay Alt P Wd7 cond iff  d5515724d8c4: P2 M Formalism Fourier Decay Alt P Wd7 cond iff  d5515724d8c4
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Wd7 cond iff  d5515724d8c4 construction uses the P2 M Formalism Fourier Decay Alt P Wd7 cond iff  d5515724d8c4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalarCommuteTransposedRMatrixEntry.lean#L26-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalarCommuteTransposedRMatrixEntry.lean#L26-L38

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd7
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]

theorem P2M_Formalism_FourierDecayAlt_P_Wd7_cond_iff__d5515724d8c4 (a : S) (i j : Fin 2) (x y : Ix S) :
    (x a = i ∧ y a = j ∧ ∀ b, b ≠ a → x b = y b) ↔ (y a = j ∧ x = Function.update y a i) := by sorry

alias «Formalism».«FourierDecayAlt».«P».«Wd7».«cond_iff'» := P2M_Formalism_FourierDecayAlt_P_Wd7_cond_iff__d5515724d8c4
