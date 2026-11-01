-- Prove2me | Theorems.Thm_QseriesFormalization_PartII_Ch08_DFinite_recurrence_fails_a3_at_zero
-- name    : QseriesFormalization.PartII.Ch08.DFinite_recurrence_fails_a3_at_zero
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T09:26:55.385355+00:00
-- url     : https://prove2.me/theorems/31ea5787-6848-40c6-afb0-90932abf4c36
-- title:
--   Counterexample: the $D$-recurrence fails for $a=3$, $q=0$, $N=0$ over $\mathbb{Q}$
-- statement:
--   Over $\mathbb{Q}$ with $q=0$, `DFinite` $0\,3\,2\ne$ `DFinite` $0\,3\,1+0^{(0+3+1)}\cdot$ `DFinite` $0\,3\,0$. That is, the recurrence $D(a,N+2)=D(a,N+1)+q^{N+a+1}D(a,N)$ for the alternating finite sum fails at $a=3$, $N=0$, so the hypothesis $a\le2$ in the recurrence lemma cannot be dropped. Chapter 8.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 8. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter08_FiniteRR.lean#L829-L837

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

/-! ### Recurrence uniqueness bridge -/

theorem QseriesFormalization.PartII.Ch08.DFinite_recurrence_fails_a3_at_zero :
    DFinite (0 : Rat) 3 2 ≠
      DFinite (0 : Rat) 3 1 + (0 : Rat) ^ (0 + 3 + 1) * DFinite (0 : Rat) 3 0 := by sorry
