-- Prove2me | Theorems.Thm_PrivSeqLearn_QueryComplexity_eq_20
-- name    : PrivSeqLearn.QueryComplexity.eq_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:14:49.235078+00:00
-- url     : https://prove2.me/theorems/7c5c190c-5c8f-4292-8179-80ea5f1aaeab
-- title:
--   Display (20), p. 20 — for an accurate strategy, I(q) ⊂ Ī(q), the union of the special intervals
-- statement:
--   Let $\phi$ be a learner strategy of length $N$ that satisfies the accuracy constraint with accuracy $\epsilon$. For every query vector $\bar q \in \mathbb R^N$,
--   $$\mathcal I(\bar q) \subseteq \bar{\mathcal I}(\bar q),$$
--   where $\bar{\mathcal I}(\bar q)$ is the union of the special intervals of $\bar q$ (intervals between consecutive points of $(0, q_1, \dots, q_N, 1)$ of length at most $\epsilon$).
--
--   The adversary can compute $\bar{\mathcal I}(\bar q)$ from the queries alone, so this bounds the learner's privacy from above.
--
--   **Formalization Note** Stated for every $\bar q$: for a query vector that no true value produces, $\mathcal I(\bar q)$ is empty. Membership in $\Phi_N$ is not assumed.
-- source:
--   Tsitsiklis, Xu, Xu, Private Sequential Learning, arXiv:1805.02136v3, p. 20, display (20)

import Mathlib
import Definitions.Def_PrivSeqLearn_QueryComplexity_Setting
import Definitions.Def_PrivSeqLearn_QueryComplexity_SpecialIntervals

namespace PrivSeqLearn.QueryComplexity

/-- Display (20) (Tsitsiklis, Xu, Xu, Private Sequential Learning, arXiv:1805.02136v3, §7.1, p. 20): for an accurate strategy, every information set is
contained in the union of the special intervals, `I(q) ⊆ Ī(q)`.

**Formalization Note** Stated for every `q : Fin N → ℝ` (for an unobservable `q` the information set
is empty). Membership in `Φ_N` is not assumed. -/
theorem eq_20 {N : ℕ} (ϵ : ℝ) (φ : Strategy N) (hacc : IsAccurate ϵ φ) (q : Fin N → ℝ) :
    infoSet φ q ⊆ specialUnion ϵ q := by sorry

end PrivSeqLearn.QueryComplexity
