-- Prove2me | Theorems.Thm_ParallelLotteries_lemma_8
-- name    : ParallelLotteries.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:36:48.655416+00:00
-- url     : https://prove2.me/theorems/4a4468cf-66d3-44ca-b099-7ad50f0cf22c
-- title:
--   Lemma 8: $h(p)=pk/(1-(1-p)^k)$ is convex (strictly for $k\ge2$)
-- statement:
--   Let $k\ge1$ and $h(p)=\dfrac{pk}{1-(1-p)^k}$ for $0<p\le1$, with $h(0)=1$. Then
--
--   1. $h$ is convex on $[0,1]$, in particular on $(0,1)$ (Lemma 8);
--   2. if $k\ge2$, $h$ is strictly convex on $[0,1]$.
--
--   Convexity of $h$ is what makes the slope $\frac{h(p_j)-h(p_i)}{p_j-p_i}$ monotone, which gives Lemma 7 and the bound $2-1/k$ in Theorem 2. For $k=1$, $h\equiv1$.
--
--   Differences from the source:
--   - generalization: convex on the open interval $(0,1)$ → convex on $[0,1]$ with $h(0):=1$; reason: Lemma 7's proof applies the convexity of $h$ on $[0,p_j]$ with $p_j$ possibly $1$; $h(0)=1$ is the limit of $h$ at $0^+$, and convexity on $[0,1]$ implies convexity on $(0,1)$
--   - generalization: (not printed) → strict convexity on $[0,1]$ for $k\ge2$; reason: it is what makes the bound of Theorem 2 strict for $k\ge2$ (the sign analysis of (65)–(66) in Lemma 8's proof gives it); it adds a clause and drops nothing
-- source:
--   Arnosti–Randolph, Alaskan Hunting License Lotteries Are Flexible and Approximately Efficient, SSRN 3370605 (preprint), App. D.2, Lemma 8, p.35

import Mathlib
import Definitions.Def_ParallelLotteries_hf

namespace ParallelLotteries

/-- **Lemma 8 (convexity of h)** — Arnosti–Randolph, SSRN 3370605 (preprint), App. D.2, p.35:
"Lemma 8. The function h defined in (60) is convex on the interval (0, 1)."
Here `h(p) = pk/(1 − (1 − p)^k)` (60), with `h(0) := 1`.

For every `k ≥ 1`:
1. `h` is convex on `[0, 1]` (in particular on `(0, 1)`, which is Lemma 8);
2. if `k ≥ 2`, `h` is strictly convex on `[0, 1]`.

**Formalization Note.** Both clauses go beyond the printed lemma: the closed interval (with
`h(0) := 1`, the continuous extension) is where Lemma 7 (p.34) applies `h`, namely on `[0, p_j]`
with `p_j` possibly `1`; strict convexity for `k ≥ 2` is what makes the bound of Theorem 2 strict.
For `k = 1`, `h ≡ 1` is convex but not strictly convex. -/
theorem lemma_8 (k : ℕ) (hk : 1 ≤ k) :
    ConvexOn ℝ (Set.Icc 0 1) (hfun k) ∧
    (2 ≤ k → StrictConvexOn ℝ (Set.Icc 0 1) (hfun k)) := by sorry

end ParallelLotteries
