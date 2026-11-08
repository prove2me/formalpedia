-- Prove2me | Theorems.Thm_TightClock_lemma_6_4
-- name    : TightClock.lemma_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:01:00.134913+00:00
-- url     : https://prove2.me/theorems/5e293c20-f898-4ce2-b204-6141118e49b7
-- title:
--   Lemma 6.4 — ticket inequalities (6.8), (6.9)
-- statement:
--   With $C(p)=1+(e^a-1)p$: for all $b,p,\alpha\in[0,1]$,
--
--   $$1-b+b\,C(p)^\alpha\le C(bp)^\alpha,\tag{6.8}$$
--
--   and if $z\ge0$ and $Mz\le1$, then
--
--   $$C(Mz)\le C(z)^M.\tag{6.9}$$
--
--   The first inequality controls the effect of revealing whether a ticket succeeds, and the second the effect of scaling its success probability by $M$.
--
--   **Formalization Note** The exponent $\alpha$ is real; the exponent $M$ is the natural number $Lq^4$.
--
--   Differences from the source:
--   - encoding: the depth $L$ of the tree, with levels $r=1,\dots,L$ in Instance 11 → the hypothesis `1 ≤ L`; reason: at $L=0$ there are no bidders and $h=a^2B/L$ divides by zero; the page's construction has $L\ge1$
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), Lemma 6.4, §6.4, p.39 (PDF p.42), eqs. (6.8), (6.9)

import Mathlib
import Definitions.Def_TightClock_C
import Definitions.Def_TightClock_M

set_option autoImplicit false

namespace TightClock

/-- Lemma 6.4 (Tickets), p.39 (PDF 42), of Afshinmehr et al., manuscript (STOC 2027 submission): the inequalities (6.8)
and (6.9). -/
theorem lemma_6_4 (q L : ℕ) (hq : 8 ≤ q) (hL : 1 ≤ L) :
    (∀ b p α : ℝ, b ∈ Set.Icc (0 : ℝ) 1 → p ∈ Set.Icc (0 : ℝ) 1 → α ∈ Set.Icc (0 : ℝ) 1 →
      1 - b + b * (C q p) ^ α ≤ (C q (b * p)) ^ α) ∧
    (∀ z : ℝ, 0 ≤ z → (M q L : ℝ) * z ≤ 1 →
      C q ((M q L : ℝ) * z) ≤ (C q z) ^ (M q L)) := by sorry

end TightClock
