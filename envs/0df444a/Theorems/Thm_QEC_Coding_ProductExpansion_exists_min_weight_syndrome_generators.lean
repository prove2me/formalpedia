-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_exists_min_weight_syndrome_generators
-- name    : QEC.Coding.ProductExpansion.exists_min_weight_syndrome_generators
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:27:27.088439+00:00
-- url     : https://prove2.me/theorems/d539a3cb-4977-41f5-a889-6917588b5e37
-- title:
--   Product Expansion: exists min weight syndrome generators
-- statement:
--   Among all rank-sized families whose syndromes span the syndrome columns,
--   one has minimum total weight on a selected coordinate set. Finite-field
--   finiteness makes the paper's minimum-weight choice an actual attained minimum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L1715-L1740
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L1715-L1740

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
omit [Fintype R] [Fintype R']

theorem QEC.Coding.ProductExpansion.exists_min_weight_syndrome_generators
    (h' : Matrix R' W F) (x : Matrix W W F) (A : Finset W) :
    ∃ C : Finset (Word F W),
      C.card = (h' * x).rank ∧
      (∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' C) ∧
      (∀ D : Finset (Word F W),
        D.card = (h' * x).rank →
        (∀ j : W, h'.mulVec (column x j) ∈ syndromeSpan h' D) →
        generatorRestrictedWeight A C ≤ generatorRestrictedWeight A D) := by sorry
