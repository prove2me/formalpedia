-- Prove2me | Theorems.Thm_SionMinimax_KKM_theorem_3_2
-- name    : SionMinimax.KKM.theorem_3_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:51:34.804622+00:00
-- url     : https://prove2.me/theorems/f6555721-ae16-48b7-998c-20b7adcff6b5
-- title:
--   Theorem 3.2, p. 173 — n + 1 points in a space of dimension k < n: the hulls of the n-point subsets meet
-- statement:
--   Let $V$ be a finite-dimensional real vector space of dimension $k$, let $n$ be a natural number with $k < n$, and let $\mathfrak A = \{a_0, \dots, a_n\}$ be a set of $n+1$ distinct points of $V$. For each $i$, write $\ulcorner \mathfrak A - \{a_i\} \urcorner$ for the convex hull of the $n$ points other than $a_i$. Then these $n+1$ convex hulls have a common point:
--
--   $$\bigcap_{i=0}^{n} \ulcorner \mathfrak A - \{a_i\} \urcorner \neq \emptyset.$$
--
--   In Sion's argument this Helly-type fact is used in contrapositive form: if the hulls of the $n$-point subfamilies of $n+1$ points have empty intersection, the points are affinely independent and span an $n$-dimensional simplex. This is what allows the open-cover KKM theorem (Theorem 3.1) to be applied inside the convex set of Lemma 3.3.
--
--   **Formalization Note** The points are an injective family $a : \{0,\dots,n\} \to V$, which encodes "$\mathfrak A$ consists of $n+1$ points", and $\mathfrak A - \{a_i\}$ is the set difference $\operatorname{range}(a) \setminus \{a_i\}$. The dimension is the linear dimension $\operatorname{finrank}_{\mathbb R} V$, as printed. The paper writes $0$ for the empty set.
-- source:
--   Sion, On general minimax theorems, Pacific J. Math. 8(1) (1958) 171–176, p. 173 (PDF p. 4), Theorem 3.2

import Mathlib

namespace SionMinimax.KKM
theorem theorem_3_2 {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (n : ℕ) (hdim : Module.finrank ℝ V < n)
    (a : Fin (n + 1) → V) (ha : Function.Injective a) :
    (⋂ i : Fin (n + 1), convexHull ℝ (Set.range a \ {a i})).Nonempty := by sorry
end SionMinimax.KKM
