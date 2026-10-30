-- Prove2me | Theorems.Thm_RamanujanNotebooks_entry_6_1
-- name    : RamanujanNotebooks.entry_6_1
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-06T22:19:18.991325+00:00
-- url     : https://prove2.me/theorems/72f14e37-1484-4d89-a979-fb1d1c57e175
-- title:
--   Euler-Maclaurin summation with the constant of the series (Hardy's form of Entry 1)
-- statement:
--   Definition (Euler-Maclaurin constant, (1.3), p. 135): for $f$ with $2n+1$ continuous derivatives on $[0,\infty)$, a real $a$ and $n\ge0$, $C_n(f,a)=\int_0^a f(t)\,dt-\tfrac12 f(0)-\sum_{k=1}^n\frac{B_{2k}}{(2k)!}f^{(2k-1)}(0)+\int_0^\infty P_{2n+1}(t)f^{(2n+1)}(t)\,dt$, where $P_m(t)=B_m(t-[t])/m!$ and the last integral is assumed to exist (Lebesgue). Theorem: let $U\supseteq[0,\infty)$ be open, $f\in C^{2n+1}(U)$, $P_{2n+1}f^{(2n+1)}$ integrable on $(0,\infty)$ and $f$ integrable between $0$ and $a$. Then for every integer $x\ge1$, $\sum_{k=1}^x f(k)=\int_a^x f(t)\,dt+\tfrac12 f(x)+\sum_{k=1}^n\frac{B_{2k}}{(2k)!}f^{(2k-1)}(x)-\int_x^\infty P_{2n+1}(t)f^{(2n+1)}(t)\,dt+C_n(f,a)$. Differs from the printed source: Ramanujan's (1.1) has an infinite Bernoulli series and no hypotheses; this is the finite formula the book puts in its place, and the open set, Lebesgue integrability and interval integrability are our rendering of the book's phrase that all indicated integrals exist. The additional statement on p. 135 that $C_n$ is independent of $n$ is not asserted here; this formula fixes $n$ and retains its corresponding remainder.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks, Part I (Springer, 1985), Chapter 6, Entry 1, pp. 134–135, eqs. (1.1), (1.3).

import Mathlib
import Definitions.Def_RamanujanNotebooks_ch06_ch06EMConstant
import Definitions.Def_RamanujanNotebooks_ch06_ch06PeriodicBernoulli

namespace RamanujanNotebooks
theorem entry_6_1 (f : ℝ → ℝ) (U : Set ℝ) (hU : IsOpen U) (hU0 : Set.Ici (0 : ℝ) ⊆ U)
    (n : ℕ) (hf : ContDiffOn ℝ ((2 * n + 1 : ℕ) : WithTop ℕ∞) f U)
    (hint : MeasureTheory.IntegrableOn
      (fun t : ℝ => ch06PeriodicBernoulli (2 * n + 1) t * iteratedDeriv (2 * n + 1) f t)
      (Set.Ioi (0 : ℝ)))
    (a : ℝ) (ha : IntervalIntegrable f MeasureTheory.volume 0 a)
    (x : ℕ) (hx : 1 ≤ x) :
    (∑ k ∈ Finset.range x, f ((k : ℝ) + 1))
      = (∫ t in a..(x : ℝ), f t) + f (x : ℝ) / 2
        + (∑ k ∈ Finset.range n,
            ((bernoulli (2 * (k + 1)) : ℚ) : ℝ) / ((2 * (k + 1)).factorial : ℝ)
              * iteratedDeriv (2 * k + 1) f (x : ℝ))
        - (∫ t in Set.Ioi (x : ℝ),
            ch06PeriodicBernoulli (2 * n + 1) t * iteratedDeriv (2 * n + 1) f t)
        + ch06EMConstant f a n := by sorry
end RamanujanNotebooks
