-- Prove2me | Theorems.Thm_QuasiPolyTrace_theorem_44
-- name    : QuasiPolyTrace.theorem_44
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:31:26.356325+00:00
-- url     : https://prove2.me/theorems/a63c2af8-97e4-478c-a815-53835cec3a7a
-- title:
--   Theorem 44 — trace reconstruction from $e^{p^{-7/3}(\log_2 n)^c}$ traces
-- statement:
--   There is a constant $c>0$ such that for every retention probability $p\in(0,1]$ and every $n\ge2$ there is a number of traces
--
--   $$
--   m\ \le\ e^{p^{-7/3}(\log_2 n)^c}
--   $$
--
--   and an algorithm that, given $m$ independent traces of an unknown $x\in\{0,1\}^n$ through the deletion channel with retention probability $p$, returns $x$ with probability at least $\tfrac23$, for every $x$.
--
--   The best previous upper bound for constant $p$ was $\exp(\tilde O(n^{1/5}))$ (Chase 2021). The algorithm may depend on $n$ and $p$ but not on $x$; the theorem bounds the number of traces, not the running time.
--
--   **Formalization Note** The statement uses the published block `OAI.TraceReconstruction`: `SufficientBudget n q (2/3) m` asks for one possibly randomized estimator that, from $m$ independent complete traces, outputs every $x$ with probability at least $2/3$. That block's parameter $q$ is the deletion probability, so $q=1-p$.
--
--   Differences from the source:
--   - reading: for any retention probability p > 0 → 0 < p ≤ 1; reason: a retention probability is a probability
--   - reading: can be done from e^{p^{−7/3}(log₂ n)^c} traces → ∃ m : ℕ, m ≤ e^{p^{−7/3}(log₂ n)^c} with SufficientBudget n (1 − p) (2/3) m; reason: a number of traces is a natural number; trace reconstruction is Definition 2 (probability ≥ 2/3)
--   - encoding: retention probability p → deletion probability 1 − p of the reused block; reason: OAI.TraceReconstruction is parametrized by the deletion probability; same instances
-- source:
--   Burudgunte, Valiant, Wang, Quasipolynomial Trace Reconstruction, manuscript of November 2, 2026 (later version of arXiv:2607.04073; sha256 9ecb6d18…), Theorem 44, p.42 (also the unnumbered Theorem of p.1)

import Mathlib
import Definitions.Def_TraceReconstruction

namespace QuasiPolyTrace

open OAI.TraceReconstruction

/-- **Theorem 44 (quasipolynomial trace reconstruction).** Burudgunte, Valiant, Wang, *Quasipolynomial Trace Reconstruction*, manuscript of November 2, 2026
(later version of arXiv:2607.04073; sha256 9ecb6d18…), Theorem 44, p.42 (also the unnumbered
"Theorem." of p.1): "There exists a constant c > 0 such that for any retention probability p > 0, trace
reconstruction on n > 1 bit strings can be done from e^{p^{−7/3}(log_2 n)^c} traces."

Statement: there is a universal `c > 0` such that for every retention probability `p ∈ (0, 1]` and every
`n ≥ 2` there is a sample budget `m ≤ e^{p^{−7/3}(log_2 n)^c}` and an algorithm that, from `m` independent
traces of an unknown `x ∈ {0,1}^n` through the deletion channel with retention probability `p`, returns
`x` with probability at least `2/3`, for every `x`.

**Formalization Note.**
* "Trace reconstruction" is Definition 2 (p.6), in the published block `OAI.TraceReconstruction`:
  `SufficientBudget n q (2/3) m` asks for one (possibly randomized) estimator, depending on `n`, `q` and
  the `m` complete traces only, that outputs every `x` with probability at least `2/3` from `m`
  independent traces of `x`. That block's `q` is the *deletion* probability, so `q = 1 − p`.
* "for any retention probability p > 0" is `p ∈ (0, 1]`: a retention probability is a probability.
* "can be done from N traces", with `N` a real number, is: some budget `m ∈ ℕ` with `m ≤ N` suffices.
* `log_2` is `Real.logb 2`; `c` is a real exponent chosen before `p` and `n`. -/
theorem theorem_44 :
    ∃ c : ℝ, 0 < c ∧ ∀ p : ℝ, 0 < p → p ≤ 1 → ∀ n : ℕ, 2 ≤ n →
      ∃ m : ℕ, (m : ℝ) ≤ Real.exp (p ^ (-(7 / 3 : ℝ)) * Real.logb 2 n ^ c) ∧
        SufficientBudget n (1 - p) (2 / 3) m := by sorry

end QuasiPolyTrace
