-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_syndromeBasis_exchange_spans
-- name    : QEC.Coding.ProductExpansion.syndromeBasis_exchange_spans
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:32:56.193816+00:00
-- url     : https://prove2.me/theorems/778eb559-7d13-4384-a645-8504bb81fc28
-- title:
--   Product Expansion: syndrome Basis exchange spans
-- statement:
--   A vector with a nonzero coordinate at `c` can replace the corresponding
--   basis vector without changing the span. This is the linear-algebra exchange
--   used by the minimum-weight syndrome-generator argument.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L1015-L1043
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L1015-L1043

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
omit [Fintype F] [DecidableEq F] [Fintype R] [Fintype R']

theorem QEC.Coding.ProductExpansion.syndromeBasis_exchange_spans
    (h' : Matrix R' W F) (C : Finset (Word F W))
    (b : Module.Basis C F (syndromeSpan h' C))
    (c : C) (z : syndromeSpan h' C)
    (hCoordinate : (b.repr z) c ≠ 0) :
    Submodule.span F (insert z (b '' {a : C | a ≠ c})) = ⊤ := by sorry
