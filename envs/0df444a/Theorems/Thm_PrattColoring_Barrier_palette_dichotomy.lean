-- Prove2me | Theorems.Thm_PrattColoring_Barrier_palette_dichotomy
-- name    : PrattColoring.Barrier.palette_dichotomy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:24:12.310059+00:00
-- url     : https://prove2.me/theorems/035a32f3-3641-49bd-b203-f6cc4e52d8c3
-- title:
--   Lemma 5.3 — two-distribution palette dichotomy
-- statement:
--   Let $k\ge3$ and $\eta\le1/(6(k-1))$. Let $p$ be an arbitrary real probability distribution on $[k]$, let $D\subseteq[k]$ be nonempty with $0<p(D)<1/2+\eta$, and let $u$ be a probability distribution supported on $D$. Then either
--   $$\exists i,j\in D:\quad u(\{i,j\})>\frac12+\frac1{6k},$$
--   or
--   $$\exists i\in D:\quad p(D\setminus\{i\})<\frac12-\eta\quad\text{and}\quad u(D\setminus\{i\})>\frac12+\frac1{3k}.$$
--   The indices $i$ and $j$ may coincide, and no positivity assumption on $\eta$ or on individual color masses is imposed.
--
--   This distributional dichotomy supplies the two alternatives used in the fixed-profile detector; it covers real distributions, not only count-normalized profiles.
--
--   Differences from the source:
--   - encoding: distributions on [k] and D, with inclusive subset notation → nonnegative real functions on Fin k summing to one, with u zero off the finite nonempty set D; reason: extension by zero is equivalent to a distribution on D; pair masses are finite set sums, so repeated indices are counted once; the upper bound and all strict conclusions are unchanged
-- source:
--   Kevin Pratt, STOC 2027 submission #690 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/690.pdf, Lemma 5.3, p. 9 (PDF p. 9); pinned source.pdf SHA256 ad5f710e4e7049a1d0cc1cd1397305575274d94aac977c67c5de74f037a0309d. Submission artifact, not accepted proceedings.

import Definitions.Def_PrattColoring_Barrier_Setting

namespace PrattColoring.Barrier

/-- Lemma 5.3, p.9: arbitrary real distributions; u is extended by zero off D.
The source uses inclusive subset notation. Neither η>0 nor i≠j is assumed. -/
theorem palette_dichotomy (k : ℕ) (hk : 3 ≤ k) (η : ℝ)
    (hη : η ≤ 1 / (6 * (k - 1 : ℝ)))
    (p u : Fin k → ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (D : Finset (Fin k)) (hD : D.Nonempty)
    (hpDpos : 0 < paletteMass p D) (hpDlt : paletteMass p D < 1 / 2 + η)
    (hu_nonneg : ∀ i, 0 ≤ u i) (hu_sum : ∑ i, u i = 1)
    (hu_support : ∀ i, i ∉ D → u i = 0) :
    (∃ i ∈ D, ∃ j ∈ D, 1 / 2 + 1 / (6 * (k : ℝ)) < paletteMass u {i, j}) ∨
      (∃ i ∈ D, paletteMass p (D.erase i) < 1 / 2 - η ∧
        1 / 2 + 1 / (3 * (k : ℝ)) < paletteMass u (D.erase i)) := by sorry

end PrattColoring.Barrier
