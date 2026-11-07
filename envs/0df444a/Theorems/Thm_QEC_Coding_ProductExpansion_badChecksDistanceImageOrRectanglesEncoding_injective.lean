-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_badChecksDistanceImageOrRectanglesEncoding_injective
-- name    : QEC.Coding.ProductExpansion.badChecksDistanceImageOrRectanglesEncoding_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:36:44.176447+00:00
-- url     : https://prove2.me/theorems/e8e924c1-7b2c-43db-886c-2730636b3953
-- title:
--   Product Expansion: bad Checks Distance Image Or Rectangles Encoding injective
-- statement:
--   The Product Expansion construction uses the bad Checks Distance Image Or Rectangles Encoding injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L1374-L1383
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansionProbability.lean#L1374-L1383

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

theorem QEC.Coding.ProductExpansion.badChecksDistanceImageOrRectanglesEncoding_injective
    (h' : Matrix R' W F) (d s m k : Nat) :
    Function.Injective
      (badChecksDistanceImageOrRectanglesEncoding
        (R := R) h' d s m k) := by sorry
