-- Prove2me | Theorems.Thm_StochasticOrders_StochasticConvexity_random_sum_closure
-- name    : StochasticOrders.StochasticConvexity.random_sum_closure
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T23:15:00.927908+00:00
-- url     : https://prove2.me/theorems/58884109-84fc-406b-b3bf-1274b46391f4
-- title:
--   Theorem 8.A.13 — closure of the icx/icv/cx orders under random sums
-- statement:
--   Let $\{Y_k, k \in \mathbb{N}_{++}\}$ be a sequence of independent and identically distributed
--   nonnegative random variables, independent of the two nonnegative discrete random variables
--   $M$ and $N$. Then
--
--   (a) $M \le_{icx}\ [\le_{icv}]\ N \implies \sum_{k=1}^{M} Y_k \le_{icx}\ [\le_{icv}]\
--   \sum_{k=1}^{N} Y_k$, and
--
--   (b) $M \le_{cx} N \implies \sum_{k=1}^{M} Y_k \le_{cx} \sum_{k=1}^{N} Y_k$.
--
--   This is a random-sum closure result: comparing the *number of terms* ($M$ vs. $N$, in the
--   icx/icv/cx order on nonnegative-integer-valued random variables) propagates to a comparison
--   of the resulting random sums. It is the formal content behind Example 8.A.2's application (a
--   homogeneous Poisson process is SIL via the semigroup property, Example 8.A.7 — not itself a
--   numbered theorem, so not drafted as a milestone here, see `STATUS.md`), stated here without
--   the parametric-family (SICX/SICV/SIL) apparatus the rest of Chapter 8 builds around, since the
--   theorem's own content and proof need none of it. The book's proof: for $\varphi$ increasing
--   convex [concave], $\psi(n) = E[\varphi(\sum_{k=1}^n Y_k)]$ is itself increasing and convex
--   [concave] in $n$ (an unnumbered fact justified by Example 8.A.4), so $M\le_{icx}[\le_{icv}]N$
--   gives $E[\psi(M)] \le E[\psi(N)]$, i.e. part (a); part (b) follows from part (a) together
--   with $E[\sum_{k=1}^M Y_k] = E[\sum_{k=1}^N Y_k]$ under $M\le_{cx}N$ (Theorem 4.A.35, a
--   Chapter 4 result not restated here).
--
--   **Formalization Note** $M, N : \Omega \to \mathbb{N}$ are nonnegative-integer-valued; the
--   $\le_{icx}/\le_{icv}/\le_{cx}$ orders applied to them are the same real-valued orders above,
--   applied after the coercion $\mathbb{N}\to\mathbb{R}$ — this chapter's pitfall 1, not a
--   separate discrete order. $\sum_{k=1}^M Y_k$ is drafted as the genuine random sum
--   `∑ k ∈ Finset.range (M ω), Y k ω`, with `Y : ℕ → Ω → ℝ` indexing `Y 0, Y 1, …` for the book's
--   `Y_1, Y_2, …` (a one-step reindexing noted explicitly, not left implicit), matching this
--   chapter's pitfall 2. Independence of $\{Y_k\}$ from $(M,N)$ jointly is drafted as
--   `IndepFun (fun ω => (M ω, N ω)) (fun ω k => Y k ω) μ`, treating the whole sequence as a
--   single `ℕ → ℝ`-valued random element. The theorem's three conjuncts (icx, icv, cx) mirror the
--   book's own single Theorem 8.A.13 with its bracketed part (a) and separate part (b), per this
--   chapter's pitfall 3.
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, p. 361, Theorem 8.A.13

import Mathlib
import Definitions.Def_StochasticOrders_StochasticConvexity_ConvexOrder
import Definitions.Def_StochasticOrders_StochasticConvexity_IcxOrder
import Definitions.Def_StochasticOrders_StochasticConvexity_IcvOrder

namespace StochasticOrders.StochasticConvexity

open MeasureTheory ProbabilityTheory

/-- Theorem 8.A.13 (Shaked & Shanthikumar, *Stochastic Orders*, Springer 2007, p. 361): let
`{Yk, k ∈ ℕ++}` be a sequence of independent and identically distributed nonnegative random
variables, independent of the two nonnegative discrete random variables `M` and `N`. Then
(a) `M ≤icx [≤icv] N ⟹ ∑_{k=1}^{M} Yk ≤icx [≤icv] ∑_{k=1}^{N} Yk`, and
(b) `M ≤cx N ⟹ ∑_{k=1}^{M} Yk ≤cx ∑_{k=1}^{N} Yk`.

`M`, `N` are nonnegative-integer-valued (`Ω → ℕ`); the `≤icx`/`≤icv`/`≤cx` orders on them are the
same real-valued orders `IcxOrder`/`IcvOrder`/`ConvexOrder` applied after the coercion `ℕ → ℝ`
(this chapter's pitfall 1: not a separate discrete order). The sequence `Y : ℕ → Ω → ℝ` indexes
`Y 0, Y 1, …` for the book's `Y1, Y2, …` (a one-step reindexing, noted here rather than left
implicit), and `∑_{k=1}^{M} Yk` is drafted as the genuine random sum `∑ k ∈ Finset.range (M ω), Y
k ω`, not a fixed-length sum with `M` substituted afterward. -/
theorem random_sum_closure {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ) (M N : Ω → ℕ)
    (hYmeas : ∀ k, Measurable (Y k)) (hMmeas : Measurable M) (hNmeas : Measurable N)
    (hYindep : iIndepFun Y μ) (hYiid : ∀ j k : ℕ, IdentDistrib (Y j) (Y k) μ μ)
    (hYnn : ∀ k, 0 ≤ᵐ[μ] Y k)
    (hIndepMN_Y : IndepFun (fun ω => (M ω, N ω)) (fun ω k => Y k ω) μ) :
    (IcxOrder μ μ (fun ω => (M ω : ℝ)) (fun ω => (N ω : ℝ)) →
      IcxOrder μ μ (fun ω => ∑ k ∈ Finset.range (M ω), Y k ω)
        (fun ω => ∑ k ∈ Finset.range (N ω), Y k ω)) ∧
    (IcvOrder μ μ (fun ω => (M ω : ℝ)) (fun ω => (N ω : ℝ)) →
      IcvOrder μ μ (fun ω => ∑ k ∈ Finset.range (M ω), Y k ω)
        (fun ω => ∑ k ∈ Finset.range (N ω), Y k ω)) ∧
    (ConvexOrder μ μ (fun ω => (M ω : ℝ)) (fun ω => (N ω : ℝ)) →
      ConvexOrder μ μ (fun ω => ∑ k ∈ Finset.range (M ω), Y k ω)
        (fun ω => ∑ k ∈ Finset.range (N ω), Y k ω)) := by sorry

end StochasticOrders.StochasticConvexity
