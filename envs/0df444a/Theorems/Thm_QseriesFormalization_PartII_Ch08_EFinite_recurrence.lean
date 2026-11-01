-- Prove2me | Theorems.Thm_QseriesFormalization_PartII_Ch08_EFinite_recurrence
-- name    : QseriesFormalization.PartII.Ch08.EFinite_recurrence
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T09:28:45.456178+00:00
-- url     : https://prove2.me/theorems/9eedf609-b914-4600-98be-ddf6adef4c3d
-- title:
--   Recurrence for the finite Rogers-Ramanujan sum side: $E_{N+2}=E_{N+1}+q^{N+a+1}E_N$
-- statement:
--   Let $R$ be a field, $q\in R$ and $a,N\in\mathbb{N}$. With `EFinite` $q\,a\,N=\sum_{j=0}^{N}q^{j^2+aj}\binom{N-j}{j}_q$ (Chan's $E_{N+1}(a)$, with Gaussian binomials),
--   $$E(a,N+2)=E(a,N+1)+q^{N+a+1}\,E(a,N).$$
--   This is the recurrence (8.2) for the finite sum side of Chapter 8's Rogers-Ramanujan polynomial identities, in zero-based indexing.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 8. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter08_FiniteRR.lean#L75-L134

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

theorem QseriesFormalization.PartII.Ch08.EFinite_recurrence (q : R) (a N : Nat) :
    EFinite q a (N + 2) =
      EFinite q a (N + 1) + q ^ (N + a + 1) * EFinite q a N := by sorry
