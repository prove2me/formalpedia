-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_mem_supportedWords_iff
-- name    : QEC.Coding.ProductExpansion.mem_supportedWords_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:25:59.081712+00:00
-- url     : https://prove2.me/theorems/d741e2c0-7fc3-479d-8532-67932154e5cc
-- title:
--   Product Expansion: mem supported Words iff
-- statement:
--   Membership in the supported-word subspace is coordinatewise vanishing
--   outside the selected support.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L819-L829
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L819-L829

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

theorem QEC.Coding.ProductExpansion.mem_supportedWords_iff (S : Finset W) (y : Word F W) :
    y ∈ supportedWords S ↔ ∀ i ∉ S, y i = 0 := by sorry
