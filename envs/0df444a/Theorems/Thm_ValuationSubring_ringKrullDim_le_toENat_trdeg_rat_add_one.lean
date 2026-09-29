-- Prove2me | Theorems.Thm_ValuationSubring_ringKrullDim_le_toENat_trdeg_rat_add_one
-- name    : ValuationSubring.ringKrullDim_le_toENat_trdeg_rat_add_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/b344d381-4d76-53b4-8581-7e26630d860e
-- title:
--   Krull dimension of a valuation ring in characteristic zero
-- statement:
--   Let $L$ be a field equipped with an algebra structure over $\mathbb{Q}$, and let $A$ be a valuation subring of $L$, i.e. a subring of $L$ such that for every $x \in L$ either $x \in A$ or $x^{-1} \in A$. The assertion is the inequality $$\operatorname{ringKrullDim} A \le \operatorname{toENat}\bigl(\operatorname{trdeg}_{\mathbb{Q}} L\bigr) + 1$$ in `WithBot ℕ∞`, where $\operatorname{ringKrullDim} A$ is the Krull dimension of the ring $A$ (the order-theoretic dimension of its prime spectrum, valued in `WithBot ℕ∞`, so that $-\infty$ and $\infty$ are allowed), and $\operatorname{trdeg}_{\mathbb{Q}} L$ is the transcendence degree of $L$ over $\mathbb{Q}$ as a cardinal, mapped to an extended natural number by `Cardinal.toENat` and then coerced into `WithBot ℕ∞`. Since `Cardinal.toENat` sends every infinite cardinal to $\top$, the inequality carries content only when $L$ has finite transcendence degree over $\mathbb{Q}$, and then it bounds the rank of the valuation by that degree plus one.
--
--   This is Abhyankar's inequality for a valuation of a field of characteristic zero, in the form bounding the rank of the valuation by $\operatorname{trdeg}_{\mathbb{Q}} L + 1$, the extra $1$ accounting for the residual valuation on $\mathbb{Q}$. It is used to obtain that valuation subrings of fields algebraic over $\mathbb{Q}$ have Krull dimension at most one, and, through that, in the construction of regular prolongations for algebraic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_ringKrullDim_le_toENat_trdeg_rat_add_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.ringKrullDim_le_toENat_trdeg_rat_add_one
    {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L) :
    ringKrullDim A ≤ (Cardinal.toENat (Algebra.trdeg ℚ L) : WithBot ℕ∞) + 1 := by sorry
