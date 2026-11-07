-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_exists_generator_with_image_distance
-- name    : QEC.Coding.ProductExpansion.exists_generator_with_image_distance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:34:05.564972+00:00
-- url     : https://prove2.me/theorems/22033e1e-6e7d-49b2-acd8-755b5bd0f466
-- title:
--   Product Expansion: exists generator with image distance
-- statement:
--   If the generator-code GV witness factor is smaller than its output-space
--   penalty, some generator matrix maps every nonzero message to weight at least
--   `d`. For positive `d`, this conclusion includes full row rank.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L772-L819
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L772-L819

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

theorem QEC.Coding.ProductExpansion.exists_generator_with_image_distance
    [DecidableEq W] (d : Nat)
    (hFactor :
      (Nat.card F) ^ Fintype.card R *
        (∑ t : Fin d,
          Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1) <
        (Nat.card F) ^ Fintype.card W) :
    ∃ g : Matrix R W F,
      ∀ a : Word F R, a ≠ 0 → d ≤ HammingWeight (g.transpose.mulVec a) := by sorry
