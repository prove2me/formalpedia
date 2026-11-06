-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_multipleRotation_val
-- name    : QEC.Coding.FiberBundle.multipleRotation_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:16:47.830077+00:00
-- url     : https://prove2.me/theorems/4a342474-efb6-4d0a-91e2-40cff02c4d83
-- title:
--   Fiber Bundle: multiple Rotation val
-- statement:
--   The Fiber Bundle construction uses the multiple Rotation val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/Core.lean#L481-L484
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/Core.lean#L481-L484

import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_FiberBundle_Core
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.multipleRotation_val
    (ell : Nat) [NeZero ell] (k : Fin ell) :
    multipleRotation ell k = (k.val * ell : Nat) := by sorry

attribute [defeq] QEC.Coding.FiberBundle.multipleRotation_val
