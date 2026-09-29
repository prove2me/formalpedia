-- Prove2me | Theorems.Thm_ValuationSubring_valuation_intCast_eq_one_of_not_dvd
-- name    : ValuationSubring.valuation_intCast_eq_one_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/75116c34-c548-5859-b218-ee212bf062a4
-- title:
--   Integers prime to q are units at a place over q
-- statement:
--   Let $K$ be a field and let $A$ be a valuation subring of $K$, with associated valuation `A.valuation` taking values in the value group of $A$ (an ordered commutative group with zero). Assume $q$ is a prime natural number whose image in $K$ has valuation strictly less than $1$, i.e. $A$ lies over $q$. Then for every integer $a$ that is not divisible by $q$ in $\mathbb{Z}$, the image of $a$ in $K$ satisfies $A.\mathrm{valuation}(a) = 1$; that is, $a$ is a unit of $A$. This is the integral analogue of the corresponding statement for natural numbers.
--
--   This is one half of the dictionary between the $q$-adic valuation of a rational number and the valuation attached to a place of $K$ over $q$: residues prime to $q$ are invertible at such a place. It is used in computing valuations of integers in terms of $q$-adic valuations, and in the verification of integrality and non-degeneracy conditions for Weierstrass models at a good prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_valuation_intCast_eq_one_of_not_dvd.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.valuation_intCast_eq_one_of_not_dvd {K : Type*} [Field K]
    (A : ValuationSubring K) {q : ℕ} (hq : q.Prime) (hA : A.valuation (q : K) < 1)
    {a : ℤ} (hqa : ¬ (q : ℤ) ∣ a) : A.valuation (a : K) = 1 := by sorry
