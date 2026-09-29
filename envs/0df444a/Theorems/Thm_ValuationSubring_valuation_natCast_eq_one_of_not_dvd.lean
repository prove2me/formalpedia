-- Prove2me | Theorems.Thm_ValuationSubring_valuation_natCast_eq_one_of_not_dvd
-- name    : ValuationSubring.valuation_natCast_eq_one_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/cb630c90-67ef-5b69-a94e-da134cb1363a
-- title:
--   Integers prime to q are units at a valuation of residue characteristic q
-- statement:
--   Let $K$ be a field and let $A$ be a valuation subring of $K$, with $A.\mathrm{valuation}$ the associated valuation on $K$ taking values in the multiplicative value group of $A$, normalised so that $A$ is exactly the set of elements of valuation $\le 1$. Let $q$ be a prime natural number whose image in $K$ satisfies $A.\mathrm{valuation}(q) < 1$, that is, $q$ lies in the maximal ideal of $A$; and let $n$ be a natural number with $q \nmid n$. Then the image of $n$ in $K$ has valuation exactly $1$, i.e. $A.\mathrm{valuation}(n) = 1$, so $n$ is a unit of $A$ (when $n$ is nonzero in $K$). No hypothesis is placed on the characteristic of $K$ or on the rank of the valuation; in particular, if $n$ happens to be $0$ in $K$ the hypotheses force this case not to occur, since $v(0) = 0 < 1$.
--
--   This is the elementary statement that a natural number prime to the residue characteristic $q$ of a valuation subring is a unit there. It is used when reducing elliptic curves and counting at a place lying over $q$: for instance in the Čerednik–Drinfel'd part of the development, to show that cardinalities of vertex stabilisers prime to $q$ have valuation one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_valuation_natCast_eq_one_of_not_dvd.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.valuation_natCast_eq_one_of_not_dvd {K : Type*} [Field K]
    (A : ValuationSubring K) {q : ℕ} (hq : q.Prime) (hA : A.valuation (q : K) < 1)
    {n : ℕ} (hqn : ¬ q ∣ n) : A.valuation (n : K) = 1 := by sorry
