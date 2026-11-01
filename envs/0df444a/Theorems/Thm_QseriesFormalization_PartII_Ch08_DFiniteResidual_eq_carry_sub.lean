-- Prove2me | Theorems.Thm_QseriesFormalization_PartII_Ch08_DFiniteResidual_eq_carry_sub
-- name    : QseriesFormalization.PartII.Ch08.DFiniteResidual_eq_carry_sub
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T09:26:27.327593+00:00
-- url     : https://prove2.me/theorems/4bdce9d4-ca95-4825-9114-9732916ecc79
-- title:
--   Telescoping form of the recurrence residual for the alternating side (case $a\le2$)
-- statement:
--   Let $R$ be a field, $q\in R$, $a\le2$, $N\in\mathbb{N}$, $j\in\mathbb{Z}$. Let `DFiniteTerm` be the $j$-th term $(-1)^jq^{j(5j+1)/2-2aj}\binom{N+a}{\lfloor(N+3a-5j)/2\rfloor}_q$ of Chan's finite alternating Gaussian-polynomial sum, and `DFiniteResidual` $q\,a\,N\,j$ its recurrence defect $D_{N+2}-D_{N+1}-q^{N+a+1}D_N$ for the term at $j$. The statement: the residual equals `DFiniteCarry` at $j$ minus `DFiniteCarry` at $j+1$. This telescoping makes the sum over $j$ of the residuals vanish; Chapter 8's Rogers-Ramanujan polynomial identity.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 8. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter08_FiniteRR.lean#L576-L655

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

theorem QseriesFormalization.PartII.Ch08.DFiniteResidual_eq_carry_sub (q : R) (a N : Nat) (ha : a ≤ 2) (j : Int) :
    DFiniteResidual q a N j = DFiniteCarry q a N j - DFiniteCarry q a N (j + 1) := by sorry
