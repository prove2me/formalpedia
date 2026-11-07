-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_card_generatorSupport_inter_le_generatorRestrictedWeight
-- name    : QEC.Coding.ProductExpansion.card_generatorSupport_inter_le_generatorRestrictedWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:26:12.077419+00:00
-- url     : https://prove2.me/theorems/d2cfa33b-be55-4714-babc-1d48151f553a
-- title:
--   Product Expansion: card generator Support inter le generator Restricted Weight
-- statement:
--   The support union inside `A` is bounded by the sum of the generators'
--   restricted Hamming weights.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L1187-L1221
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L1187-L1221

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
omit [Fintype F] [Fintype R] [Fintype R']

theorem QEC.Coding.ProductExpansion.card_generatorSupport_inter_le_generatorRestrictedWeight
    (A : Finset W) (C : Finset (Word F W)) :
    (generatorSupportOn A C).card ≤ generatorRestrictedWeight A C := by sorry
