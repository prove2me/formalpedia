-- Prove2me | Theorems.Thm_ValuationSubring_ringKrullDim_le_ringKrullDim_comap_add_trdeg
-- name    : ValuationSubring.ringKrullDim_le_ringKrullDim_comap_add_trdeg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/cf3d6bef-cf7a-5b93-953f-e308f6c3da95
-- title:
--   Abhyankar's inequality for Krull dimensions of valuation rings
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra (the structure map $K \to L$ being automatically an embedding of fields), and let $A$ be a valuation subring of $L$, i.e. a subring of $L$ such that for every $x \in L$ either $x \in A$ or $x^{-1} \in A$. Write $A \cap K$ for `A.comap (algebraMap K L)`, the preimage of $A$ under $K \to L$, which is a valuation subring of $K$. The assertion is the inequality
--   $$\dim A \;\le\; \dim (A \cap K) \;+\; \operatorname{trdeg}_K L$$
--   of Krull dimensions, where $\dim$ is `ringKrullDim`, valued in $\mathbb{N}\cup\{\pm\infty\}$ (for a valuation ring this is the rank of the associated valuation, the order type of its chain of prime ideals), and where the transcendence degree $\operatorname{trdeg}_K L$, a priori a cardinal, is first mapped to the extended natural numbers by `Cardinal.toENat` — so infinite transcendence degree becomes $\infty$ — and then coerced into $\mathbb{N}\cup\{\pm\infty\}$, the sum and the order being those of that type. In particular the inequality carries no information when $L/K$ has infinite transcendence degree.
--
--   This is the rank form of Abhyankar's inequality: the rank of a valuation of $L$ exceeds the rank of its restriction to $K$ by at most the transcendence degree of $L$ over $K$; in particular the rank does not grow in algebraic extensions and grows by at most one in a simple transcendental extension. It is used in the project to bound the rank of valuation rings of function fields of curves, notably in the specialisation that a valuation subring of a field of transcendence degree one over $\mathbb{Q}$ has Krull dimension at most one, and in the construction of good constant reductions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_ringKrullDim_le_ringKrullDim_comap_add_trdeg.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.ringKrullDim_le_ringKrullDim_comap_add_trdeg
    {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L) :
    ringKrullDim A ≤ ringKrullDim (A.comap (algebraMap K L)) +
      (Cardinal.toENat (Algebra.trdeg K L) : WithBot ℕ∞) := by sorry
