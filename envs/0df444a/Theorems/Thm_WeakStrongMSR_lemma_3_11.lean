-- Prove2me | Theorems.Thm_WeakStrongMSR_lemma_3_11
-- name    : WeakStrongMSR.lemma_3_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:26:30.617723+00:00
-- url     : https://prove2.me/theorems/d808085b-e3d6-4c91-810c-3207c5c55ec4
-- title:
--   Lemma 3.11 — $2m$ draws with point masses $\le 1/(8m)$ give more than $m$ distinct outcomes, except with probability $2^{-m}$
-- statement:
--   Let $m\ge0$.
--
--   1. Let $p$ be a probability distribution with $\max_xp_x\le 1/(8m)$. In $2m$ independent draws from $p$,
--   $$\Pr[\text{at most } m \text{ distinct outcomes}]\le 2^{-m}.$$
--   2. The same bound holds for $2m$ sequential draws in which, given the earlier draws, every outcome has conditional probability at most $1/(8m)$.
--
--   The sequential form is what the sampling analysis uses, since the LP weights change between rounds.
--
--   **Formalization Note** Probabilities are extended nonnegative reals. For $m=0$ the hypothesis is vacuous and both bounds are trivial.
--
--   Differences from the source: none.
-- source:
--   Friggstad–Jamshidian–Vakilian, Minimum Sum-of-Radii Clustering with Strong and Weak Oracles (manuscript, STOC 2027 submission, sha256 5f8fbaf3…67e8f92a0), Lemma 3.11, p.13 (PDF 14)

import Mathlib
import Definitions.Def_WeakStrongMSR_Draws

open scoped Classical

set_option autoImplicit false

namespace WeakStrongMSR

/-- **Lemma 3.11** (Friggstad–Jamshidian–Vakilian, *Minimum Sum-of-Radii Clustering with Strong and Weak Oracles*
(manuscript, sha256 5f8fbaf3…67e8f92a0), p.13, PDF p.14).
"Let p be a probability distribution with max_x p_x ≤ 1/(8m). In 2m independent draws from p,
Pr[at most m distinct outcomes] ≤ 2^{−m}. The same conclusion holds for sequential draws whose
conditional probability of each outcome is always at most 1/(8m)."

For every `m`:
1. if every outcome of `p` has probability at most `1/(8m)`, then `2m` independent draws from `p`
   have at most `m` distinct outcomes with probability at most `2^{−m}`;
2. the same holds for `2m` sequential draws in which each draw, given the earlier draws, has every
   outcome with probability at most `1/(8m)`.

**Formalization Note.** Probabilities are in `ℝ≥0∞`; for `m = 0`, `1/(8m) = ∞` and both claims
are trivial. The outcome space is any type. -/
theorem lemma_3_11 {α : Type*} (m : ℕ) :
    (∀ p : PMF α, (∀ x, p x ≤ ((8 * m : ℕ) : ENNReal)⁻¹) →
      (iidDraws p (2 * m)).toOuterMeasure {xs | xs.toFinset.card ≤ m} ≤ (2⁻¹ : ENNReal) ^ m) ∧
    (∀ κ : List α → PMF α, (∀ hist x, κ hist x ≤ ((8 * m : ℕ) : ENNReal)⁻¹) →
      (seqDraws κ (2 * m)).toOuterMeasure {xs | xs.toFinset.card ≤ m} ≤
        (2⁻¹ : ENNReal) ^ m) := by sorry

end WeakStrongMSR
