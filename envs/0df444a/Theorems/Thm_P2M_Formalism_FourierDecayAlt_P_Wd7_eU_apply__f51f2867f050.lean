-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Wd7_eU_apply__f51f2867f050
-- name    : P2M_Formalism_FourierDecayAlt_P_Wd7_eU_apply__f51f2867f050
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:13:57.746803+00:00
-- url     : https://prove2.me/theorems/2dc2e70a-53ec-451c-b221-4be4ec5982ed
-- title:
--   P2 M Formalism Fourier Decay Alt P Wd7 e U apply  f51f2867f050: P2 M Formalism Fourier Decay Alt P Wd7 e U apply  f51f2867f050
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Wd7 e U apply  f51f2867f050 construction uses the P2 M Formalism Fourier Decay Alt P Wd7 e U apply  f51f2867f050 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalarCommuteTransposedRMatrixEntry.lean#L46-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalarCommuteTransposedRMatrixEntry.lean#L46-L50

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

theorem P2M_Formalism_FourierDecayAlt_P_Wd7_eU_apply__f51f2867f050 (a : S) (i j : Fin 2) (x y : Ix S) :
    (eU a i j : SlopeTestRemainingChoices S A) x y = if y a = j ∧ x = Function.update y a i then 1 else 0 := by sorry

alias «Formalism».«FourierDecayAlt».«P».«Wd7».«eU_apply'» := P2M_Formalism_FourierDecayAlt_P_Wd7_eU_apply__f51f2867f050
