-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_exists_supported_syndrome_lift_of_mem_span
-- name    : QEC.Coding.ProductExpansion.exists_supported_syndrome_lift_of_mem_span
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:26:01.565192+00:00
-- url     : https://prove2.me/theorems/4be5ca19-6771-4557-bd09-f07dfbe1be42
-- title:
--   Product Expansion: exists supported syndrome lift of mem span
-- statement:
--   Membership in the span of generator syndromes has an actual word lift
--   supported inside the generators' support union.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L856-L877
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L856-L877

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

theorem QEC.Coding.ProductExpansion.exists_supported_syndrome_lift_of_mem_span
    (h' : Matrix R' W F) (C : Finset (Word F W)) (z : R' → F)
    (hz : z ∈ syndromeSpan h' C) :
    ∃ y : Word F W,
      (∀ i ∉ generatorSupport C, y i = 0) ∧ h'.mulVec y = z := by sorry
