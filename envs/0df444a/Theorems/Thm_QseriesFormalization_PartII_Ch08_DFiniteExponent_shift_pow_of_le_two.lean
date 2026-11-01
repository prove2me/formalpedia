-- Prove2me | Theorems.Thm_QseriesFormalization_PartII_Ch08_DFiniteExponent_shift_pow_of_le_two
-- name    : QseriesFormalization.PartII.Ch08.DFiniteExponent_shift_pow_of_le_two
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T09:26:15.99662+00:00
-- url     : https://prove2.me/theorems/d6d8621f-fcf6-4410-aade-1a10321b5b50
-- title:
--   Exponent bookkeeping for the finite alternating Rogers-Ramanujan side (shifted $j\to j+1$)
-- statement:
--   Let $R$ be a field, $q\in R$, $a\le2$, $N\in\mathbb{N}$, $j\in\mathbb{Z}$. Let $L=\lfloor(N+3a-5j)/2\rfloor$ (`DFiniteLower`) and $e_a(j)=j(5j+1)/2-2aj$ (`DFiniteExponent`). Assume $N+3a-5j$ is odd (the stated parity condition `hpar`, a nonzero residue mod 2) and $1\le L\le N+a+1$. Then
--   $$q^{e_a(j+1)}\,q^{L-1}=q^{e_a(j)}\,q^{N+a+1-L}.$$
--   A pure exponent identity used in the telescoping proof of the finite Rogers-Ramanujan polynomial identity (Chapter 8).
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 8. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter08_FiniteRR.lean#L435-L503

import Definitions.Def_QseriesFormalization_Pending_Chapter08_FiniteRR
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

open QseriesFormalization
open QseriesFormalization.PartII
open QseriesFormalization.PartII.Ch08

variable {R : Type*} [Field R]

/-! ### Chan's finite alternating Gaussian-polynomial side -/

/-! ### Alternating-side recurrence for the Rogers-Ramanujan cases -/

theorem QseriesFormalization.PartII.Ch08.DFiniteExponent_shift_pow_of_le_two (q : R) (a N : Nat) (ha : a ≤ 2)
    (j : Int)
    (hpar : ((N : Int) + 3 * (a : Int) - 5 * j) % 2 ≠ 0)
    (hb1 : 1 ≤ DFiniteLower a N j)
    (hb2 : DFiniteLower a N j ≤ (N + a : Int) + 1) :
    q ^ DFiniteExponent a (j + 1) * q ^ (DFiniteLower a N j - 1).toNat =
      q ^ DFiniteExponent a j *
        q ^ (((N + a : Nat) : Int) + 1 - DFiniteLower a N j).toNat := by sorry
