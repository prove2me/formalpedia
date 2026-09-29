-- Prove2me | Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_fixing_ne_of_not_dvd_valuation
-- name    : ValuationSubring.exists_mem_inertiaSubgroupIn_fixing_ne_of_not_dvd_valuation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/470bcbef-07d5-5a26-b422-3031d896eb41
-- title:
--   Ramification of a Kummer extension witnessed by an inertia element
-- statement:
--   Let $L'$ be an intermediate field of $\mathbb{Q}$ in a fixed algebraic closure $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` which is a number field, let $p_0$ be a prime number, let $x$ be a unit of $L'$ (that is, a nonzero element of $L'$), and let $v$ be a height-one prime of the ring of integers $\mathcal{O}_{L'}$. Let $q$ be a prime number whose image in $\mathcal{O}_{L'}$ lies in the prime ideal of $v$, so that $v$ lies over $q$. Assume that $p_0$ does not divide the integer attached to the $v$-adic valuation $v(x) \in \mathbb{Z}^{\mathrm{multiplicative}}$ of the unit $x$, and let $y \in \overline{\mathbb{Q}}$ satisfy $y^{p_0} = x$, the image of $x$ in $\overline{\mathbb{Q}}$. Then there is a valuation subring $P$ of $\overline{\mathbb{Q}}$ such that the image of $q$ in $\overline{\mathbb{Q}}$ is a nonunit of $P$, together with an element $\sigma$ of $\mathrm{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$ lying in the image of the inertia subgroup of $P$ over $\mathbb{Q}$ under the inclusion of the decomposition subgroup of $P$ over $\mathbb{Q}$, such that $\sigma z = z$ for every $z \in L'$ while $\sigma y \neq y$.
--
--   This is the standard Kummer-theoretic ramification statement: if the $v$-adic valuation of $x$ is prime to $p_0$, then $L'(x^{1/p_0})/L'$ is ramified at $v$, here recorded in the form of an explicit inertia element inside $\mathrm{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$ for the notion of inertia used by the unramifiedness conditions of the library. It is used by [`AlgebraicClosure.exists_uniform_level_of_characters_unramified_outside`](thm.html#AlgebraicClosure.exists_uniform_level_of_characters_unramified_outside) to show that a character unramified outside a finite set has a Kummer generator whose valuations outside that set are divisible by $p_0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_fixing_ne_of_not_dvd_valuation.lean

import Definitions.Def_FLTPrelim_Ramification
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.SelmerGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField IsDedekindDomain

theorem ValuationSubring.exists_mem_inertiaSubgroupIn_fixing_ne_of_not_dvd_valuation
    (L' : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField L']
    (p₀ : ℕ) (hp₀ : p₀.Prime) (x : (L' : Type)ˣ) (v : HeightOneSpectrum (𝓞 L'))
    (q : ℕ) (hq : q.Prime) (hqv : (q : 𝓞 L') ∈ v.asIdeal)
    (hv : ¬ ((p₀ : ℤ) ∣ Multiplicative.toAdd (v.valuationOfNeZero x)))
    (y : AlgebraicClosure ℚ) (hy : y ^ p₀ = ((x : L') : AlgebraicClosure ℚ)) :
    ∃ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q ∧
      ∃ σ ∈ P.inertiaSubgroupIn ℚ, (∀ z : L', σ z = z) ∧ σ y ≠ y := by sorry
