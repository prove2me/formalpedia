-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_card_generatorFiber_mul_field_pow_length_eq_total
-- name    : QEC.Coding.ProductExpansion.card_generatorFiber_mul_field_pow_length_eq_total
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:36:21.743204+00:00
-- url     : https://prove2.me/theorems/6fb4badb-643b-470d-9900-5f13488af815
-- title:
--   Product Expansion: card generator Fiber mul field pow length eq total
-- statement:
--   Every fixed nonzero message and target word has the same exact number of
--   generator matrices mapping the message to that target.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L648-L661
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L648-L661

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Projection
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
omit [Fintype R']

theorem QEC.Coding.ProductExpansion.card_generatorFiber_mul_field_pow_length_eq_total
    (a : Word F R) (ha : a ≠ 0) (y : Word F W) :
    Nat.card {g : Matrix R W F // g.transpose.mulVec a = y} *
        (Nat.card F) ^ Fintype.card W = Nat.card (Matrix R W F) := by sorry
