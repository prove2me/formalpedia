-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_wordLinearMapTranspose_matrixToLin_single
-- name    : QEC.Coding.FiberBundle.wordLinearMapTranspose_matrixToLin_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:19:45.116438+00:00
-- url     : https://prove2.me/theorems/3fad81d2-e4d2-4b22-a545-ce69623cdf67
-- title:
--   Fiber Bundle: word Linear Map Transpose matrix To Lin single
-- statement:
--   The Fiber Bundle construction uses the word Linear Map Transpose matrix To Lin single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L219-L237
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L219-L237

import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionDistance
import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
open scoped BigOperators
universe u v
variable {baseZero baseOne fiberZero fiberOne : Type u}
variable [Fintype baseZero] [DecidableEq baseZero]
variable [Fintype baseOne] [DecidableEq baseOne]
variable [Fintype fiberZero] [DecidableEq fiberZero]
variable [Fintype fiberOne] [DecidableEq fiberOne]
variable (D : Data baseZero baseOne fiberZero fiberOne)
local notation "R" => baseSupportRelation D

theorem QEC.Coding.FiberBundle.wordLinearMapTranspose_matrixToLin_single
    {F Row Col : Type*} [Field F] [Fintype F]
    [Fintype Row] [DecidableEq Row]
    [Fintype Col] [DecidableEq Col]
    (M : Matrix Row Col F) (r : Row) :
    wordLinearMapTranspose (Matrix.toLin' M) (Pi.single r 1) =
      fun c => M r c := by sorry
