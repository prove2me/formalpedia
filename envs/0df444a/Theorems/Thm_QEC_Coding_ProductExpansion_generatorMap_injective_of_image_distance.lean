-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_generatorMap_injective_of_image_distance
-- name    : QEC.Coding.ProductExpansion.generatorMap_injective_of_image_distance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:36:04.005866+00:00
-- url     : https://prove2.me/theorems/fe530c80-e503-4d85-b171-54463fef8c4c
-- title:
--   Product Expansion: generator Map injective of image distance
-- statement:
--   Positive image distance forces the generator map to be injective.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L894-L907
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L894-L907

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
omit [Fintype F] [Fintype R']

theorem QEC.Coding.ProductExpansion.generatorMap_injective_of_image_distance
    (g : Matrix R W F) (d : Nat) (hPositive : 0 < d)
    (hImage : ∀ a : Word F R, a ≠ 0 →
      d ≤ HammingWeight (g.transpose.mulVec a)) :
    Function.Injective (fun a : Word F R => g.transpose.mulVec a) := by sorry
