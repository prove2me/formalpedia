-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_localStar_restrictedWeight_ge
-- name    : QEC.Coding.ProductExpansion.localStar_restrictedWeight_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:04:31.124387+00:00
-- url     : https://prove2.me/theorems/bdddbf31-a3a5-4626-b70e-8afaa054286a
-- title:
--   Product Expansion: local Star restricted Weight ge
-- statement:
--   The source's `J₂/J₃` dichotomy: either many heavy rows supply the
--   rectangle weight, or the large agreement block invokes product expansion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalStarExpansion.lean#L368-L402
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalStarExpansion.lean#L368-L402

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalStarExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [DecidableEq W] [Fintype R] [Fintype R']
omit [Fintype R] [Fintype R']

theorem QEC.Coding.ProductExpansion.localStar_restrictedWeight_ge
    (h : Matrix R W F) (h' : Matrix R' W F)
    (f t : Matrix W W F) (A B J₂ J₃ : Finset W)
    (d m s : Nat) (beta : ℝ)
    (hExpand : ProductExpanding h h' s (2 * m) beta)
    (hKernel : ProductKernel h h' t) (hNonzero : t ≠ 0)
    (hMinimal : Fintype.card W - 2 * m ≤ J₃.card →
      IsDeltaMinimal h h' (beta * Fintype.card W) t)
    (hA : Fintype.card W - m < A.card)
    (hB : Fintype.card W - m < B.card)
    (hCover : B ⊆ J₂ ∪ J₃)
    (hJ₂B : J₂ ⊆ B) (hJ₃B : J₃ ⊆ B)
    (hHeavy : ∀ i ∈ J₂, d ≤ 2 * HammingWeight (row f i))
    (hDistance : 4 * m ≤ d)
    (hScale : 4 * s ≤ m * d)
    (hAgree : ∀ i ∈ J₃, ∀ j ∈ A, f i j = t i j) :
    s ≤ restrictedWeight f B A := by sorry
