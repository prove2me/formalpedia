-- Prove2me | Theorems.Thm_QseriesFormalization_PartII_Ch08_second_order_recurrence_unique
-- name    : QseriesFormalization.PartII.Ch08.second_order_recurrence_unique
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T09:29:18.122521+00:00
-- url     : https://prove2.me/theorems/75a5292d-68d6-4f65-866c-b096d4cab63e
-- title:
--   Uniqueness for a second-order recurrence $F(N+2)=F(N+1)+c(N)F(N)$
-- statement:
--   Let $R$ be a field and $F,G,c:\mathbb{N}\to R$. Suppose $F(0)=G(0)$, $F(1)=G(1)$, and both satisfy $F(N+2)=F(N+1)+c(N)F(N)$ and $G(N+2)=G(N+1)+c(N)G(N)$ for all $N$. Then $F(N)=G(N)$ for all $N$. A two-line induction used in Chapter 8 to compare the two sides of the finite Rogers-Ramanujan identities.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 8. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter08_FiniteRR.lean#L738-L761

import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Chapter 8 finite Rogers-Ramanujan sum side

Chan's Section 8.1 writes
`E_n(a) = sum_j q^(j^2 + a*j) [n-j-1 choose j]_q` and proves the
second-order recurrence
`E_{n+1}(a) = E_n(a) + q^(n+a-1) E_{n-1}(a)`.

The zero-based definition below is `EFinite q a N = E_{N+1}(a)`.
-/

variable {R : Type*} [Field R]

/-! ### Chan's finite alternating Gaussian-polynomial side -/

/-! ### Alternating-side recurrence for the Rogers-Ramanujan cases -/

/-! ### Recurrence uniqueness bridge -/

theorem QseriesFormalization.PartII.Ch08.second_order_recurrence_unique (F G c : Nat → R)
    (h0 : F 0 = G 0) (h1 : F 1 = G 1)
    (hF : ∀ N, F (N + 2) = F (N + 1) + c N * F N)
    (hG : ∀ N, G (N + 2) = G (N + 1) + c N * G N) :
    ∀ N, F N = G N := by sorry
