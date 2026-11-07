-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_parityCheckCode_generatorImageParityCheck_distance
-- name    : QEC.Coding.ProductExpansion.parityCheckCode_generatorImageParityCheck_distance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:34:21.299441+00:00
-- url     : https://prove2.me/theorems/68060e65-078b-4af6-9c51-df4b275887ed
-- title:
--   Product Expansion: parity Check Code generator Image Parity Check distance
-- statement:
--   A generator-image distance lower bound transfers to the constructed
--   parity-check presentation of exactly that image code.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L875-L890
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L875-L890

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

theorem QEC.Coding.ProductExpansion.parityCheckCode_generatorImageParityCheck_distance
    (g : Matrix R W F) (d : Nat)
    (hImage : ∀ a : Word F R, a ≠ 0 →
      d ≤ HammingWeight (g.transpose.mulVec a)) :
    ∀ c : Word F W,
      c ∈ (parityCheckCode (generatorImageParityCheck g)).carrier →
      c ≠ 0 → d ≤ HammingWeight c := by sorry
