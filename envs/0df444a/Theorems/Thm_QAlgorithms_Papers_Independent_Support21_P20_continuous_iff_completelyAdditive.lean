-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P20_continuous_iff_completelyAdditive
-- name    : QAlgorithms.Papers.Independent.Support21.P20.continuous_iff_completelyAdditive
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:55:19.724194+00:00
-- url     : https://prove2.me/theorems/5dda994d-4821-4e12-8edc-3fc8009335b4
-- title:
--   Continuous and completely additive finite valuations
-- statement:
--   Let $A$ be a complete Boolean algebra and let $\nu:A\to[0,\infty)$ have finite values. A positive valuation is normalized at zero, monotone, and satisfies the modular identity. It is continuous when it preserves the supremum of every nonempty directed subset. Assuming classical choice,
--
--   $$\nu\text{ is a continuous valuation}\quad\Longleftrightarrow\quad\nu\text{ is a completely additive valuation}.$$
--
--   Complete additivity means that for every small pairwise disjoint family $(a_i)_{i\in I}$, including the empty family, the sum converges absolutely and $\nu(\bigvee_i a_i)=\sum_i\nu(a_i)$. This identifies the order and measure notions of continuity on Boolean locales.
-- source:
--   Gelfand-type duality for commutative von Neumann algebras, arXiv:2005.05284v3, PDF p. 10, Lemma 2.21

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P20

namespace QAlgorithms.Papers.Independent.Support21.P20

open Set Filter

open scoped NNReal

universe u v

/-- Lemma 2.21, PDF pp.10–11 (classical choice): continuous iff completely additive. -/
theorem continuous_iff_completelyAdditive (A : Type u) [CompleteBooleanAlgebra A]
    (nu : A → ℝ≥0) :
    IsPositiveContinuousValuation nu ↔ IsCompletelyAdditiveValuation nu := by sorry

end QAlgorithms.Papers.Independent.Support21.P20
