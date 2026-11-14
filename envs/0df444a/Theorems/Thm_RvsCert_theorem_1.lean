-- Prove2me | Theorems.Thm_RvsCert_theorem_1
-- name    : RvsCert.theorem_1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-12T06:43:05.55122+00:00
-- url     : https://prove2.me/theorems/03145fa5-25ad-4a6a-82b5-34bc2715d85f
-- title:
--   Theorem 1 — a total $f$ on $\tilde O(n^3)$ bits with $C(f)=\Omega(n^2)$, $R(f)=\tilde O(n)$, $Q(f)=\tilde O(\sqrt n)$
-- statement:
--   There are constants $A$, $c>0$ and $k$ such that for every $n>0$ there is a total Boolean function $f:\{0,1\}^N\to\{0,1\}$ with
--
--   1. $N\le A\,n^3(\log_2 n+1)^k$,
--   2. $C(f)\ge c\,n^2$,
--   3. $R(f)\le A\,n(\log_2 n+1)^k$, and
--   4. $Q(f)\le A\sqrt n\,(\log_2 n+1)^k$,
--
--   where $C$ is the certificate complexity and $R$, $Q$ are the bounded-error (error $1/3$ on every input) randomized and quantum query complexities. In particular $R(f)=\tilde O(\sqrt{C(f)})$ and $Q(f)=\tilde O(C(f)^{1/4})$, answering the question whether a total function can have $R(f)\ll C(f)$.
--
--   **Formalization Note** $R$ and $Q$ take values in $\mathbb N\cup\{\infty\}$; each upper bound is stated as the existence of a natural number $T$ with $R(f)\le T$ (resp. $Q(f)\le T$) satisfying the bound.
--
--   Differences from the source:
--   - reading: N = Õ(n³), C(f) = Ω(n²), R(f) = Õ(n), Q(f) = Õ(√n) for all n > 0 → ∃ A, c > 0, k before n with N ≤ A·n³·(log₂ n+1)^k, c·n² ≤ C f, R, Q ≤ A·n·(log₂ n+1)^k, A·√n·(log₂ n+1)^k; reason: asymptotic notation over the family in n is uniform; the +1 keeps the polylog factor positive at n = 1; a common A and k for the three Õ bounds is equivalent (take the maximum)
--   - encoding: f : {0,1}^N → {0,1}; R(f), Q(f) → f : (Fin N → Bool) → Bool; randQC, quantQC in ℕ∞ stated as ∃ T : ℕ, … ≤ T ∧ T ≤ …; reason: Lean convention; same instances
-- source:
--   Ben-David–Kothari, Randomized query complexity can beat certificate complexity, arXiv:2609.15063v1, Theorem 1, p.1

import Mathlib
import Definitions.Def_RvsCert_C
import Definitions.Def_RvsCert_randQC
import Definitions.Def_RvsCert_quantQC

namespace RvsCert

/-- **Theorem 1** (p.1 of Ben-David–Kothari, *Randomized query complexity can beat certificate complexity*, arXiv:2609.15063v1): "For all n > 0, there is a total Boolean
function f : {0, 1}^N → {0, 1} with N = Õ(n³), such that C(f) = Ω(n²), R(f) = Õ(n), and
Q(f) = Õ(√n)." There are constants `A`, `c > 0` and `k` such that for every `n > 0` there are
`N` and a total `f : (Fin N → Bool) → Bool` with `N ≤ A·n³·(log₂ n + 1)^k`, `C(f) ≥ c·n²`,
`R(f) ≤ A·n·(log₂ n + 1)^k` and `Q(f) ≤ A·√n·(log₂ n + 1)^k`.

**Formalization Note.** `R` and `Q` are bounded-error (`1/3` on every input) worst-case query
complexities in `ℕ∞`, stated as `∃ T : ℕ, … ≤ T ∧ T ≤ …`; `Õ(g)` is read as
`≤ A·g·(log₂ n + 1)^k` with constants chosen before `n`. -/
theorem theorem_1 :
    ∃ (A c : ℝ) (k : ℕ), 0 < c ∧ ∀ n : ℕ, 0 < n →
      ∃ (N : ℕ) (f : (Fin N → Bool) → Bool),
        (N : ℝ) ≤ A * (n : ℝ) ^ 3 * (Real.logb 2 n + 1) ^ k ∧
        c * (n : ℝ) ^ 2 ≤ (C f : ℝ) ∧
        (∃ T : ℕ, randQC f ≤ T ∧ (T : ℝ) ≤ A * (n : ℝ) * (Real.logb 2 n + 1) ^ k) ∧
        (∃ T : ℕ, quantQC f ≤ T ∧ (T : ℝ) ≤ A * Real.sqrt n * (Real.logb 2 n + 1) ^ k) := by sorry

end RvsCert
