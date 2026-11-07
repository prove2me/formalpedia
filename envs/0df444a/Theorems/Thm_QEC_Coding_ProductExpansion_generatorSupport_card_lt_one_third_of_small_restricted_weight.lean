-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_generatorSupport_card_lt_one_third_of_small_restricted_weight
-- name    : QEC.Coding.ProductExpansion.generatorSupport_card_lt_one_third_of_small_restricted_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:26:34.335067+00:00
-- url     : https://prove2.me/theorems/434c1d43-fd82-49e7-86a0-acfcc03b0b34
-- title:
--   Product Expansion: generator Support card lt one third of small restricted weight
-- statement:
--   The converse counting direction needed for the light-generator prefix:
--   total restricted weight below `d/6` confines the entire support union to
--   fewer than `d/3` coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L1258-L1282
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L1258-L1282

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

theorem QEC.Coding.ProductExpansion.generatorSupport_card_lt_one_third_of_small_restricted_weight
    (d m : Nat) (hLength : d ≤ Fintype.card W) (hSmallM : 6 * m ≤ d)
    (A : Finset W) (hLargeA : Fintype.card W - m ≤ A.card)
    (C : Finset (Word F W))
    (hWeight : (generatorRestrictedWeight A C : ℝ) < (d : ℝ) / 6) :
    ((generatorSupport C).card : ℝ) < (d : ℝ) / 3 := by sorry
