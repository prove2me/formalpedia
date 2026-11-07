-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_choose_power_sum_le
-- name    : QEC.Coding.ProductExpansion.choose_power_sum_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:34:57.281496+00:00
-- url     : https://prove2.me/theorems/99c128a8-bf0d-4572-b254-6a4d870c7763
-- title:
--   Product Expansion: choose power sum le
-- statement:
--   A uniform elementary bound on the binomial/power sum used for sparse
--   rectangle matrices.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L200-L218
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L200-L218

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

theorem QEC.Coding.ProductExpansion.choose_power_sum_le
    (n out s q : Nat) (hq : 0 < q) :
    (∑ t : Fin s, Nat.choose n t.1 * q ^ (out + t.1)) ≤
      s * (n + 1) ^ s * q ^ (out + s) := by sorry
