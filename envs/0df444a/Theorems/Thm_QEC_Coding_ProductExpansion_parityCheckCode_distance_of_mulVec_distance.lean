-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_parityCheckCode_distance_of_mulVec_distance
-- name    : QEC.Coding.ProductExpansion.parityCheckCode_distance_of_mulVec_distance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:34:03.700201+00:00
-- url     : https://prove2.me/theorems/c98066d3-ebe5-46d0-9e7f-135b8d660245
-- title:
--   Product Expansion: parity Check Code distance of mul Vec distance
-- statement:
--   A kernel-weight lower bound is exactly the distance hypothesis used by
--   the parity-check-code formulation of product expansion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L1703-L1714
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L1703-L1714

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
omit [Fintype R] [Fintype R']

theorem QEC.Coding.ProductExpansion.parityCheckCode_distance_of_mulVec_distance
    (h : Matrix R W F) (d : Nat)
    (hDistance : ∀ c : Word F W,
      h.mulVec c = 0 → c ≠ 0 → d ≤ HammingWeight c) :
    ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c := by sorry
