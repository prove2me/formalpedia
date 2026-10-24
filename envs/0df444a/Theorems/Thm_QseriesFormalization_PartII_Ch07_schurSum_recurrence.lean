-- Prove2me | Theorems.Thm_QseriesFormalization_PartII_Ch07_schurSum_recurrence
-- name    : QseriesFormalization.PartII.Ch07.schurSum_recurrence
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T09:24:23.833463+00:00
-- url     : https://prove2.me/theorems/8d285921-27e5-443e-bddb-3347593d84d5
-- title:
--   Schur's recurrence for $\sum_n q^{n^2}\binom{N-n}{n}_q$
-- statement:
--   For $q\in\mathbb{C}$ and $N\in\mathbb{N}$, let $S_N(q)=\sum_{n=0}^{N}q^{n^2}\binom{N-n}{n}_q$ be Schur's finite sum, where $\binom{a}{b}_q$ is the Gaussian binomial coefficient (and $N-n$ is natural-number subtraction). Then
--   $$S_{N+2}(q)=S_{N+1}(q)+q^{N+1}S_N(q).$$
--   This recurrence (proved by a carry-telescoping argument) is the key step in Schur's proof of a finite form of the Rogers-Ramanujan identities, Chapter 7.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 7. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter07_RRStep1.lean#L130-L184

import Definitions.Def_QseriesFormalization_Chapter07_RRStep1
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Chapter 7 — Rogers-Ramanujan Step 1 (Schur finite identity + Tannery)

Isolated module for the deepest R-R step: the Schur polynomial recurrence,
its identification with the finite Gaussian sum, and the Tannery limit
yielding `rrJInf 1 q · (q;q)_∞ = ∑'_j (-1)^j q^(j(5j+1)/2)`.

See `docs/RR_step1_schur.md`.
-/

open QseriesFormalization
open QseriesFormalization.PartII
open QseriesFormalization.PartII.Ch07

open Filter Topology

/-! ### Schur recurrence for `schurSum`

The crux of Step 1: `schurSum q (N+2) = schurSum q (N+1) + q^(N+1)·schurSum q N`.

Proof (verified by hand, exponent algebra):

`S q (N+2) = ∑_n q^(n²)·[N+2-n choose n]_q`. Apply gaussianBinom Pascal
(`[m+1 choose k+1]_q = [m choose k+1]_q + q^(m-k)·[m choose k]_q` with
`m=N+1-n, k=n-1`):

`[N+2-n choose n]_q = [N+1-n choose n]_q + q^(N+2-2n)·[N+1-n choose n-1]_q`

So `S q (N+2) = S q (N+1) + ∑_n q^(n²+N+2-2n)·[N+1-n choose n-1]_q`.
Reindex `n = m+1`: `q^((m+1)²+N+2-2(m+1)) = q^(m²+N+1)`, and
`[N+1-(m+1) choose m]_q = [N-m choose m]_q`. So the second sum
`= q^(N+1)·∑_m q^(m²)·[N-m choose m]_q = q^(N+1)·S q N`. ∎

The Lean formalization of this Finset reindex + Pascal split is in
`schurSum_recurrence` (below), and `rrPoly_eq_schurSum` follows by
two-step induction. -/

theorem QseriesFormalization.PartII.Ch07.schurSum_recurrence (q : ℂ) (N : ℕ) :
    schurSum q (N + 2) = schurSum q (N + 1) + q ^ (N + 1) * schurSum q N := by sorry
