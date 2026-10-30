-- Prove2me | Theorems.Thm_QseriesFormalization_PartII_Ch07_tendsto_gaussianBinom_sub
-- name    : QseriesFormalization.PartII.Ch07.tendsto_gaussianBinom_sub
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T09:25:15.414417+00:00
-- url     : https://prove2.me/theorems/42eb65ff-f5bb-4265-9148-400f766ff1b6
-- title:
--   Limit of $\binom{N-n}{n}_q$ as $N\to\infty$ is $1/(q;q)_n$
-- statement:
--   For $q\in\mathbb{C}$ with $|q|<1$ and a natural number $n$, the Gaussian binomial coefficients $\binom{N-n}{n}_q$ (with natural-number subtraction) converge as $N\to\infty$ to $1/(q;q)_n$, where $(q;q)_n=\prod_{j=1}^n(1-q^j)$. This pointwise limit is used in Chapter 7 (Step 5 of the Rogers-Ramanujan proof) to pass from the finite Schur sum to the infinite series.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 7. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter07_RRStep1.lean#L239-L276

import Definitions.Def_QseriesFormalization_DefCoreQSeries
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

/-! ### Tannery LHS — pointwise gaussianBinom limit -/

theorem QseriesFormalization.PartII.Ch07.tendsto_gaussianBinom_sub (q : ℂ) (hq : ‖q‖ < 1) (n : ℕ) :
    Tendsto (fun N : ℕ => gaussianBinom q (N - n) n) atTop
      (𝓝 (1 / qPochhammer q n)) := by sorry
