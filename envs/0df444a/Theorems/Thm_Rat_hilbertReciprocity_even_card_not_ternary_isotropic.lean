-- Prove2me | Theorems.Thm_Rat_hilbertReciprocity_even_card_not_ternary_isotropic
-- name    : Rat.hilbertReciprocity_even_card_not_ternary_isotropic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/c866fa7e-d22f-5d4c-bc81-07a87bcec9b0
-- title:
--   Hilbert reciprocity over ℚ: parity of anisotropic places
-- statement:
--   Let $a, b \in \mathbb{Q}$ be nonzero. The assertion is that there exists a finite set $S$ of height one primes $v$ of the ring of integers of $\mathbb{Q}$ (that is, of maximal ideals of $\mathbb{Z}$, so of finite places of $\mathbb{Q}$) with the following two properties. First, a height one prime $v$ belongs to $S$ if and only if the ternary quadratic form $z^2 - a x^2 - b y^2$ is anisotropic over the completion $\mathbb{Q}_v$ of $\mathbb{Q}$ at $v$: there is no triple $(z,x,y)$ of elements of `v.adicCompletion ℚ`, other than those with $z = x = y = 0$, satisfying $z^2 - a x^2 - b y^2 = 0$, the coefficients $a$ and $b$ being taken in $\mathbb{Q}_v$ via the structure map. Thus $S$ is exactly the set of finite anisotropic places, and in particular that set is finite. Second, the cardinality of $S$, increased by $1$ when $a < 0$ and $b < 0$ and otherwise unchanged, is even.
--
--   This is Hilbert's product formula $\prod_{v \le \infty} (a,b)_v = 1$ over $\mathbb{Q}$, written as a parity statement about the finite places at which the ternary form $z^2 - ax^2 - by^2$ has no nontrivial zero, the correction term accounting for the unique archimedean place, where anisotropy happens exactly when $a$ and $b$ are both negative. It is used in the treatment of quaternion algebras over $\mathbb{Q}$, where it controls the admissible ramification sets and feeds into the recognition of an algebra ramified exactly at a prescribed finite set of places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rat_hilbertReciprocity_even_card_not_ternary_isotropic.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IsDedekindDomain NumberField

theorem Rat.hilbertReciprocity_even_card_not_ternary_isotropic
    (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)),
      (∀ v, v ∈ S ↔
        ¬ ∃ z x y : v.adicCompletion ℚ, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
          z ^ 2 - (algebraMap ℚ (v.adicCompletion ℚ) a) * x ^ 2
            - (algebraMap ℚ (v.adicCompletion ℚ) b) * y ^ 2 = 0) ∧
      Even (S.card + if (a < 0 ∧ b < 0) then 1 else 0) := by sorry
