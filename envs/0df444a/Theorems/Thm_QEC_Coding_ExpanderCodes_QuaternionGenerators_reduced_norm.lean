-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_reduced_norm
-- name    : QEC.Coding.ExpanderCodes.QuaternionGenerators.reduced_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:29:58.903037+00:00
-- url     : https://prove2.me/theorems/5cf9010d-80d1-4fb0-9dac-6f8107bee442
-- title:
--   Quaternion Generators: reduced norm
-- statement:
--   The norm dictated by the multiplication and conjugation operations.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionGenerators.lean#L66-L71
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionGenerators.lean#L66-L71

import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.Group.Conj
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionGenerators
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
universe u
variable {K : Type u} [Field K]

theorem QEC.Coding.ExpanderCodes.QuaternionGenerators.reduced_norm (epsilon y : K) (q : Model epsilon y) :
    (star q * q).re = q.re ^ 2 - epsilon * q.imI ^ 2 -
      (1 + y) * q.imJ ^ 2 + epsilon * (1 + y) * q.imK ^ 2 := by sorry
