-- Prove2me | Theorems.Thm_P2M_GlobalTheory_eigDim_aeval_toLin__0786b496869e
-- name    : P2M_GlobalTheory_eigDim_aeval_toLin__0786b496869e
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:12:14.183579+00:00
-- url     : https://prove2.me/theorems/1552de15-7ff1-4507-b76f-318c16f93825
-- title:
--   P2 M Global Theory eig Dim aeval to Lin  0786b496869e: P2 M Global Theory eig Dim aeval to Lin  0786b496869e
-- statement:
--   The P2 M Global Theory eig Dim aeval to Lin  0786b496869e construction uses the P2 M Global Theory eig Dim aeval to Lin  0786b496869e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankKerAevalEqNatDegreeMulFinrankEigenspaceAl.lean#L57-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankKerAevalEqNatDegreeMulFinrankEigenspaceAl.lean#L57-L60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankKerAevalEqNatDegreeMulFinrankEigenspaceAl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory

theorem P2M_GlobalTheory_eigDim_aeval_toLin__0786b496869e {K : Type} [Field K] {n : Type} [Fintype n]
    [DecidableEq n] (M : Matrix n n K) (f : K[X]) :
    aeval (Matrix.toLin' M) f = Matrix.toLin' (aeval M f) := by sorry

alias «GlobalTheory».«eigDim_aeval_toLin'» := P2M_GlobalTheory_eigDim_aeval_toLin__0786b496869e
