-- Prove2me | Theorems.Thm_PrivSeqLearn_QueryComplexity_private_lower_bound
-- name    : PrivSeqLearn.QueryComplexity.private_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:14:17.778982+00:00
-- url     : https://prove2.me/theorems/d644a268-0447-4086-9920-93c9cd1ded6f
-- title:
--   p. 21 — every (ϵ,δ,L)-private strategy of length N has N ≥ log(δ/ϵ) + 2L − 4
-- statement:
--   Fix $\epsilon > 0$, $\delta > 0$ and an integer $L \ge 2$ with $2\epsilon < \delta \le 1/L$. Let $\phi$ be a learner strategy of any length $N$ whose query maps take values in $[0,1)$. If $\phi$ is $(\epsilon, \delta, L)$-private, then
--   $$N \ge \left\lceil \log_2 \frac{\delta}{\epsilon} \right\rceil + 2L - 4.$$
--
--   This is the second term of the lower bound in Theorem 4.1. In the paper it follows from Lemma 7.1 (at least $\lceil\log_2(\delta/\epsilon)\rceil$ queries in $(0,\delta)$), display (20), and the cover bound (at least $2L-3$ special queries in $[\delta,1]$, one of which may be the artificial query $q_{N+1} = 1$).
--
--   **Formalization Note** Stated for every private strategy, not about $N^*$. Distinct queries are not assumed (a strengthening; the paper's argument does not use distinctness). The bound is computed in $\mathbb Z$, so $2L - 4$ does not truncate.
-- source:
--   Tsitsiklis, Xu, Xu, Private Sequential Learning, arXiv:1805.02136v3, p. 21, end of §7.2 (K ≥ 2L − 3 and the decrement by 1)

import Mathlib
import Definitions.Def_PrivSeqLearn_QueryComplexity_Setting

namespace PrivSeqLearn.QueryComplexity

/-- The second term of the lower bound in Theorem 4.1 (Tsitsiklis, Xu, Xu, Private Sequential Learning, arXiv:1805.02136v3, p. 21, end of §7.2): in the regime
of Theorem 4.1, every `(ϵ, δ, L)`-private learner strategy of any length `N` whose query maps take
values in `[0, 1)` has `N ≥ ⌈log₂(δ/ϵ)⌉ + 2L − 4`.

**Formalization Note** Stated for every strategy, not on `N*` (a lower bound on an `sInf` over an
empty set would be vacuous). Distinctness of queries is not assumed: a disclosed strengthening, as
the paper's argument never uses it. The bound is in `ℤ`, so `2L − 4` does not truncate. -/
theorem private_lower_bound (ϵ δ : ℝ) (L : ℕ) (hϵ : 0 < ϵ) (hδ : 0 < δ) (hL : 2 ≤ L)
    (h2ϵδ : 2 * ϵ < δ) (hδL : δ ≤ 1 / (L : ℝ))
    (N : ℕ) (φ : Strategy N) (hφ : QueriesInUnit φ) (hpriv : IsPrivate ϵ δ L φ) :
    ⌈Real.logb 2 (δ / ϵ)⌉ + 2 * (L : ℤ) - 4 ≤ (N : ℤ) := by sorry

end PrivSeqLearn.QueryComplexity
