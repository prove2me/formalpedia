-- Prove2me | Theorems.Thm_QseriesFormalization_PartII_Ch08_DFinite_recurrence_of_a_le_two
-- name    : QseriesFormalization.PartII.Ch08.DFinite_recurrence_of_a_le_two
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T09:26:58.561658+00:00
-- url     : https://prove2.me/theorems/130f9d29-d9ad-4f28-ac1e-bbd0ab393cb8
-- title:
--   Recurrence $D(a,N+2)=D(a,N+1)+q^{N+a+1}D(a,N)$ for the alternating finite sum, $a\le2$
-- statement:
--   Let $R$ be a field, $q\in R$, $a\le 2$ and $N\in\mathbb{N}$. Let `DFinite` $q\,a\,N=\sum_{j\in\mathbb{Z}}(-1)^jq^{j(5j+1)/2-2aj}\binom{N+a}{\lfloor(N+3a-5j)/2\rfloor}_q$ (a finite sum, terms with out-of-range lower index vanish). Then
--   $$D(a,N+2)=D(a,N+1)+q^{N+a+1}D(a,N).$$
--   The restriction $a\le2$ is needed (see the $a=3$ counterexample). Chapter 8, finite Rogers-Ramanujan identities.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 8. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter08_FiniteRR.lean#L694-L715

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

theorem QseriesFormalization.PartII.Ch08.DFinite_recurrence_of_a_le_two (q : R) (a N : Nat) (ha : a ≤ 2) :
    DFinite q a (N + 2) =
      DFinite q a (N + 1) + q ^ (N + a + 1) * DFinite q a N := by sorry
