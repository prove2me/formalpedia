-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_restrictedWeight_ge_of_productExpanding_agreement
-- name    : QEC.Coding.ProductExpansion.restrictedWeight_ge_of_productExpanding_agreement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:37:25.81076+00:00
-- url     : https://prove2.me/theorems/0e13878d-e65e-4783-a5aa-6664ba6c20ed
-- title:
--   Product Expansion: restricted Weight ge of product Expanding agreement
-- statement:
--   Second branch of the local-star proof: agreement with a product-expanding
--   word on a large subrectangle transfers its lower bound to the face word.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalStarExpansion.lean#L260-L286
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalStarExpansion.lean#L260-L286

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalStarExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [DecidableEq W] [Fintype R] [Fintype R']
omit [DecidableEq W] [Fintype R] [Fintype R']

theorem QEC.Coding.ProductExpansion.restrictedWeight_ge_of_productExpanding_agreement
    (h : Matrix R W F) (h' : Matrix R' W F)
    (f t : Matrix W W F) (A B J₃ : Finset W)
    (s m : Nat) (beta : ℝ)
    (hExpand : ProductExpanding h h' s (2 * m) beta)
    (hKernel : ProductKernel h h' t) (hNonzero : t ≠ 0)
    (hMinimal : IsDeltaMinimal h h'
      (beta * Fintype.card W) t)
    (hA : Fintype.card W - 2 * m ≤ A.card)
    (hJ₃ : Fintype.card W - 2 * m ≤ J₃.card)
    (hJ₃B : J₃ ⊆ B)
    (hAgree : ∀ i ∈ J₃, ∀ j ∈ A, f i j = t i j) :
    s ≤ restrictedWeight f B A := by sorry
