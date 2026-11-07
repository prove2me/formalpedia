-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_exists_code_projection_of_restriction_injective
-- name    : QEC.Coding.ProductExpansion.exists_code_projection_of_restriction_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:29:32.22612+00:00
-- url     : https://prove2.me/theorems/de280482-79fa-49f3-98f6-47447a2e475b
-- title:
--   Product Expansion: exists code projection of restriction injective
-- statement:
--   Injective coordinate restriction yields a linear codeword projection using only those coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L129-L153
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ProductExpansion.lean#L129-L153

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
omit [DecidableEq F] [Fintype R]

theorem QEC.Coding.ProductExpansion.exists_code_projection_of_restriction_injective
    (h : Matrix R W F) (A : Finset W)
    (hInjective : Function.Injective (codeRestriction h A)) :
    ∃ T : Word F W →ₗ[F] Word F W,
      (∀ c : Word F W, c ∈ (parityCheckCode h).carrier → T c = c) ∧
      (∀ x : Word F W, (∀ i ∈ A, x i = 0) → T x = 0) ∧
      (∀ x : Word F W, T x ∈ (parityCheckCode h).carrier) := by sorry
