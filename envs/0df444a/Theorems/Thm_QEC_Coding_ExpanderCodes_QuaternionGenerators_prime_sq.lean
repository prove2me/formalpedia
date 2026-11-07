-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_prime_sq
-- name    : QEC.Coding.ExpanderCodes.QuaternionGenerators.prime_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:43:55.303403+00:00
-- url     : https://prove2.me/theorems/a91cd92a-a7ae-4b22-856f-ab69fc2e9e6d
-- title:
--   Quaternion Generators: prime sq
-- statement:
--   The Quaternion Generators construction uses the prime sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionGenerators.lean#L61-L63
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionGenerators.lean#L61-L63

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

theorem QEC.Coding.ExpanderCodes.QuaternionGenerators.prime_sq (epsilon y : K) (hOne : 1 + y ≠ 0) :
    prime epsilon y ^ 2 = ((epsilon * y / (1 + y) : K) : Model epsilon y) := by sorry
