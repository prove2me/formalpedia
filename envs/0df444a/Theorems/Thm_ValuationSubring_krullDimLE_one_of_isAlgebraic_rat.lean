-- Prove2me | Theorems.Thm_ValuationSubring_krullDimLE_one_of_isAlgebraic_rat
-- name    : ValuationSubring.krullDimLE_one_of_isAlgebraic_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/aff43a73-e33d-541d-9256-5ba4e4402da5
-- title:
--   Valuation rings of algebraic extensions of ℚ have Krull dimension ≤ 1
-- statement:
--   Let $L$ be a field equipped with a $\mathbb{Q}$-algebra structure such that $L$ is algebraic over $\mathbb{Q}$ (so $L$ is a number field, an algebraic closure $\overline{\mathbb{Q}}$, or any intermediate algebraic extension), and let $A$ be a valuation subring of $L$, that is, a subring $A \subseteq L$ with the property that for every $x \in L$ either $x \in A$ or $x^{-1} \in A$. The assertion is `Ring.KrullDimLE 1 A`: the Krull dimension of the ring $A$ is at most $1$, i.e. every chain of prime ideals of $A$ has length at most $1$. Equivalently, the valuation of $L$ attached to $A$ has rank at most one: either $A = L$ (the trivial valuation, of dimension $0$) or the maximal ideal of $A$ is its only nonzero prime ideal. No separatedness, completeness or discreteness assumption is imposed on $A$, and the value group is not assumed discrete; the conclusion is a bound on the dimension, not the statement that $A$ is a discrete valuation ring.
--
--   This is the rank statement for valuations of algebraic extensions of $\mathbb{Q}$, the characteristic-zero, transcendence-degree-zero case of Abhyankar's inequality. It is used in the project wherever valuation rings of $\overline{\mathbb{Q}}$ or of number fields must be known to be one-dimensional, for instance in the treatment of integrality and specialisation conditions on modular curves and in the analysis of Néron models of $J_0$ at a prime $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_krullDimLE_one_of_isAlgebraic_rat.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.krullDimLE_one_of_isAlgebraic_rat
    {L : Type*} [Field L] [Algebra ℚ L] [Algebra.IsAlgebraic ℚ L] (A : ValuationSubring L) :
    Ring.KrullDimLE 1 A := by sorry
