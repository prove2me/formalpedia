-- Prove2me | Theorems.Thm_PalmQueueing_Ordering_palm_count_expansion
-- name    : PalmQueueing.Ordering.palm_count_expansion
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T03:26:36.058953+00:00
-- url     : https://prove2.me/theorems/c3d0025d-ad99-4753-80b1-e1907c4cabec
-- title:
--   Lemma 4.4.1 — the Palm expansion of a functional of the count
-- statement:
--   **Lemma 4.4.1.** Let $N$ be a stationary point process with finite intensity $\lambda$ and Palm
--   probability $P^0$, with points $T_n$ ($T_0 \le 0 < T_1$). For all functions
--   $f : \mathbb{R}_+ \to \mathbb{R}$ with $f(0) = 0$, and for all $x > 0$,
--   $$ E_P[f(N[0,x))] = \sum_{n=0}^{\infty}\big(f(n+1) - 2f(n) + f((n-1)^+)\big)\,
--   \lambda E_{P^0}(x - T_n)^+ , \tag{4.4.1} $$
--   whenever the series converges absolutely.
--
--   A stationary expectation of a functional of the count in a window is expanded into a series of
--   **second differences** of $f$ against Palm expectations of the residual window $(x - T_n)^+$.
--   For $f$ convex every coefficient is non-negative, so the expansion is monotone in the quantities
--   $E_{P^0}(x-T_n)^+$; this is what turns a $\le_{cx}$ comparison of the Palm distributions
--   $T_n[P^0]$ into a $\le_{cx}$ comparison of the stationary counts $N[0,x)[P]$ (Property 4.4.1).
--
--   **Formalization Note.** The book states (4.4.1) "for all functions $f$" without a convergence
--   qualification. Read literally this fails: the partial sums differ from
--   $\sum_{k\le M} f(k)P(N[0,x)=k)$ by the boundary term $f(M+1)a_M - f(M)a_{M+1}$, with
--   $a_n = \lambda E_{P^0}(x-T_n)^+$, which need not vanish for heavy-tailed counts and sparse $f$ even
--   when $E_P|f(N[0,x))| < \infty$. The statement therefore assumes
--   $\sum_n |f(n+1) - 2f(n) + f((n-1)^+)|\,a_n < \infty$, which covers the book's use (convex $f$ with
--   finite expectation, all terms non-negative).
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, p. 295, Lemma 4.4.1

import Mathlib
import Definitions.Def_PalmQueueing_Palm_PointProcess

/-!
# Lemma 4.4.1: the Palm expansion of a functional of the count (§4.4, p.295)
-/

namespace PalmQueueing.Ordering

open MeasureTheory
open PalmQueueing.Palm

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Lemma 4.4.1** (p.295). Let `N` be a stationary point process with finite intensity. For all
functions `f : ℝ₊ → ℝ` with `f(0) = 0`, and for all `x > 0`,

`(4.4.1)  E_P[f(N[0,x))] = Σ_{n=0}^{∞} ( f(n+1) − 2f(n) + f((n−1)⁺) ) λ E_{P⁰}(x − T_n)⁺`.

A stationary expectation of a functional of the count in a window is expanded into a series of
**second differences** of `f` against Palm expectations of the residual window `(x − T_n)⁺`. The
second difference is what makes the lemma useful: `f` convex means every coefficient
`f(n+1) − 2f(n) + f((n−1)⁺)` is non-negative, so the whole expansion is monotone in the quantities
`E_{P⁰}(x − T_n)⁺` — which is exactly what Property 4.4.1 needs to turn a `≤_cx` comparison of the
`T_n[P⁰]` into a `≤_cx` comparison of the counts `N[0,x)[P]`.

That equivalence, Property 4.4.1, is the point of §4.4:

> (i) `T_n[P⁰] ≤_cx T̃_n[P̃⁰]` for all `n ≥ 1`;  (ii) `N[0,x)[P] ≤_cx Ñ[0,x)[P̃]` for all
> `x ∈ ℝ₊`

are equivalent. The section's Example 4.4.1, "Feller's paradox revisited", shows that the
corresponding statement for `≤_i` is **false** — the Palm order does not pass to the stationary
one — so the restriction to `≤_cx` is essential and this lemma is where it enters.

`f(0) = 0` is a hypothesis, not a normalisation: the coefficient at `n = 0` is
`f(1) − 2f(0) + f(0) = f(1) − f(0)`, and the series is arranged around it.

**Correction of the page (recorded in `HARD.md`).** The page states (4.4.1) "for all functions
`f`" without saying in what sense the series converges, and read literally it is false: the
second differences telescope, `Σ_{n ≤ M} Δ²f(n) a_n = Σ_{k ≤ M} f(k) P(N[0,x) = k)
+ f(M+1) a_M − f(M) a_{M+1}` with `a_n = λE_{P⁰}(x − T_n)⁺ = E_P(N[0,x) − n)⁺`, and for a mixed
Poisson `N` with heavy-tailed intensity and `f` supported on a sparse set the boundary term does
not vanish although `E_P|f(N[0,x))| < ∞`. The theorem is therefore stated under the hypothesis
that the series of (4.4.1) converges absolutely, `Σ_n |Δ²f(n)| λE_{P⁰}(x − T_n)⁺ < ∞`, which
covers the use the book makes of it (convex `f`, where every term is non-negative) and makes the
right-hand side an honest sum rather than Lean's `tsum` of a non-summable family (`= 0`). -/
theorem palm_count_expansion (S : PalmSetting Ω) (f : ℝ → ℝ) (hf0 : f 0 = 0) (x : ℝ) (hx : 0 < x)
    (hsum : Summable fun n : ℕ =>
      |f ((n : ℝ) + 1) - 2 * f (n : ℝ) + f (max ((n : ℝ) - 1) 0)| *
        (S.lam * ∫ ω, max (x - S.N.T (n : ℤ) ω) 0 ∂S.P0)) :
    ∫ ω, f ((S.N.count ω (Set.Ico (0 : ℝ) x)).toReal) ∂S.P
      = ∑' n : ℕ,
          (f ((n : ℝ) + 1) - 2 * f (n : ℝ) + f (max ((n : ℝ) - 1) 0)) *
            (S.lam * ∫ ω, max (x - S.N.T (n : ℤ) ω) 0 ∂S.P0) := by sorry

end PalmQueueing.Ordering
