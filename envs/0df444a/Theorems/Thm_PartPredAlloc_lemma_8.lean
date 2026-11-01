-- Prove2me | Theorems.Thm_PartPredAlloc_lemma_8
-- name    : PartPredAlloc.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:16:28.355033+00:00
-- url     : https://prove2.me/theorems/9105f376-3070-41a6-9a96-c9b3434782f7
-- title:
--   Lemma 8, p.21 — the error terms of the proof of Theorem 1 are $O(\epsilon)$ (under (5))
-- statement:
--   Let $\alpha=10+2\sqrt6$, $\bar\epsilon=1/24$, $k=16$, $\Delta=\alpha\sqrt{b\log n}$, $\theta=\frac{1-p}{2-a}$ and $\epsilon=\frac1{a(1-p)p}\sqrt{\frac{\log n}b}$. There is a constant $K$ such that for all $n\ge3$, $1\le b\le n$ and $a,p\in(0,1)$ satisfying the standing assumption (5),
--
--   $$
--   b>\frac1{\bar\epsilon^2}\,\frac{\log n}{a^2(1-p)^2p^2},
--   $$
--
--   all four error terms are below $K\epsilon$:
--
--   $$
--   \text{(a) }\frac{(1-a)\Delta}{ab},\qquad\text{(b) }\frac{5\Delta}{\theta b},\qquad\text{(c) }\frac{\frac k{p^2}\log n}{ab},\qquad\text{(d) }\frac{\frac k{p^2}\log n+4\Delta}{\theta b}.
--   $$
--
--   This shows that the error terms of the case analysis in the proof of Theorem 1 are all of the order of $\epsilon$.
--
--   Differences from the source:
--   - reading: Lemma 8 / the display after (5) printed without hypotheses → assumption (5): b > (1/ε̄²) log n / (a²(1−p)²p²); reason: both sit inside the proof of Theorem 1 after "without loss of generality, we assume (5)" (p.16), and their proofs use it; without (5), Lemma 8(c) is false (its ratio to ε is k(1−p)√(log n / b)/p, unbounded as p → 0 at n = 3, b = 1)
--   - encoding: O(ε) (Definition 2: ∃ k, f(x) < k g(x) for all x) → ∃ K, chosen before n, b, a, p (and the instance), with the bound for all of them; reason: Definition 2 quantifies one constant over the whole domain
--   - encoding: four statements f_i = O(ε) → one K for the four terms; reason: equivalent: take the maximum of the four constants
--   - encoding: b units (b ≥ 0) → 1 ≤ b; reason: the printed terms ∆/(ab), ∆/(θb), (log n)/(ab) and ε = √(log n / b)/(a(1−p)p) are undefined at b = 0
-- source:
--   Hwang, Jaillet, Manshadi, Online Resource Allocation under Partially Predictable Demand, arXiv:1810.00447v1, Lemma 8, p.21; assumption (5), p.16; proof pp.ec14–ec15

import Mathlib
import Definitions.Def_PartPredAlloc_alphaL1

namespace PartPredAlloc

/-- **Lemma 8** (Hwang–Jaillet–Manshadi, arXiv:1810.00447v1, Lemma 8, p.21; proof pp.ec14–ec15),
under the standing assumption (5) of the proof of Theorem 1 (p.16). The error terms in Lemmas 3, 5
and 7 are `O(ε)`, with `ε = (1/(a(1 − p)p)) √(log n / b)`:
(a) `(1 − a)∆/(ab) = O(ε)`, (b) `5∆/(θb) = O(ε)`, (c) `((k/p²) log n)/(ab) = O(ε)` and
(d) `((k/p²) log n + 4∆)/(θb) = O(ε)`.

**Formalization Note.** `O(·)` is Definition 2 (p.12): one constant `K` with `f < K g` on the whole
domain; here one `K` serves all four terms (take the maximum of four), and it is chosen before
`n, b, a, p`. The domain is `n ≥ 3`, `1 ≤ b ≤ n`, `a, p ∈ (0, 1)` with (5):
`b > (1/ε̄²) log n / (a²(1 − p)²p²)`. `log` is the natural logarithm. -/
theorem lemma_8 :
    ∃ K : ℝ, ∀ (n b : ℕ) (a p : ℝ), 3 ≤ n → 1 ≤ b → b ≤ n → 0 < a → a < 1 → 0 < p → p < 1 →
      (b : ℝ) > 1 / epsBar ^ 2 * (Real.log n / (a ^ 2 * (1 - p) ^ 2 * p ^ 2)) →
      (1 - a) * Delta n b / (a * b) < K * epsErr n b a p ∧
      5 * Delta n b / (theta a p * b) < K * epsErr n b a p ∧
      kL1 / p ^ 2 * Real.log n / (a * b) < K * epsErr n b a p ∧
      (kL1 / p ^ 2 * Real.log n + 4 * Delta n b) / (theta a p * b) < K * epsErr n b a p := by sorry

end PartPredAlloc
