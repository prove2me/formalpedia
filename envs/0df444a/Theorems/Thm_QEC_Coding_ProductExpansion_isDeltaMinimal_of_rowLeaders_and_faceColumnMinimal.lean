-- Prove2me | Theorems.Thm_QEC_Coding_ProductExpansion_isDeltaMinimal_of_rowLeaders_and_faceColumnMinimal
-- name    : QEC.Coding.ProductExpansion.isDeltaMinimal_of_rowLeaders_and_faceColumnMinimal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:04:24.378713+00:00
-- url     : https://prove2.me/theorems/c48d6d29-2189-4710-9f7a-babc0711c019
-- title:
--   Product Expansion: is Delta Minimal of row Leaders and face Column Minimal
-- statement:
--   The coset-leader minimality step in PK22's active-vertex argument. Rows of
--   `t` are exact local-code coset leaders. Its columns agree with the face matrix
--   `f` on all but `2m` rows, while local minimality of the global chain permits a
--   face-column decrease of at most two. Hence `t` is `beta*w`-minimal once that
--   budget dominates `4m+2`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalStarExpansion.lean#L294-L363
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LocalStarExpansion.lean#L294-L363

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalStarExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [DecidableEq W] [Fintype R] [Fintype R']
omit [DecidableEq W] [Fintype R] [Fintype R']

theorem QEC.Coding.ProductExpansion.isDeltaMinimal_of_rowLeaders_and_faceColumnMinimal
    (h : Matrix R W F) (h' : Matrix R' W F)
    (f t : Matrix W W F) (J₃ : Finset W)
    (m : Nat) (beta : ℝ)
    (hJ₃ : Fintype.card W - 2 * m ≤ J₃.card)
    (hAgree : ∀ i ∈ J₃, ∀ j, f i j = t i j)
    (hRowLeaders : ∀ i c,
      c ∈ (parityCheckCode h).carrier →
      HammingWeight (row t i) ≤ HammingWeight (row t i + c))
    (hFaceColumns : ∀ j c,
      c ∈ (parityCheckCode h').carrier →
      (HammingWeight (column f j) : ℝ) ≤
        HammingWeight (column f j + c) + 2)
    (hBudget : 4 * (m : ℝ) + 2 ≤ beta * Fintype.card W) :
    IsDeltaMinimal h h' (beta * Fintype.card W) t := by sorry
