-- Prove2me | Theorems.Thm_VapnikChervonenkis_GrowthFunction_theorem1_growth_dichotomy
-- name    : VapnikChervonenkis.GrowthFunction.theorem1_growth_dichotomy
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:37:21.589708+00:00
-- url     : https://prove2.me/theorems/a67625e3-d6cd-447d-93c3-dbfa490f96b1
-- title:
--   Theorem 1 — m^S(r) is either identically 2^r or majorized by r^n + 1
-- statement:
--   Let $X$ be a set and $S$ a nonempty collection of subsets of $X$, with growth function $m^S(r) = \max \Delta^S(x_1, \dots, x_r)$, the maximal number of different subsamples that the sets of $S$ induce in a sample of size $r$. Then one of the following holds:
--
--   1. $m^S(r) = 2^r$ for every $r \ge 0$; or
--   2. there is a positive integer $n$, the first value of $r$ for which the equation $m^S(r) = 2^r$ is violated (that is, $m^S(n) \ne 2^n$ and $m^S(r) = 2^r$ for all $r < n$), such that
--
--   $$
--   m^S(r) \le r^n + 1 \qquad \text{for every } r \ge 0 .
--   $$
--
--   Theorem 1 says that the growth function of any class of events is either exponential or bounded by a polynomial, whose degree is the size of the smallest sample on which the class fails to induce every subsample. In the paper this dichotomy makes the bound $4 m^S(2l) e^{-\varepsilon^2 l/8}$ of Theorem 2 tend to zero whenever $m^S$ is not identically $2^r$.
--
--   **Formalization Note.** The class $S$ is assumed nonempty. The paper calls $n$ "a positive constant"; for $S = \emptyset$ every index is $0$, the first violation occurs at $r = 0$, and $n$ would not be positive. The minimality of $n$ is part of the statement: a bound $r^n + 1$ for an arbitrary violating $n$ would be weaker. Samples are sequences `Fin r → X` and `growthFunction` is the supremum of the index over them; the case $r = 0$ reads $m^S(0) = 1 \le 0^n + 1$.
-- source:
--   Vapnik and Chervonenkis, On the Uniform Convergence of Relative Frequencies of Events to Their Probabilities, Theory Probab. Appl. 16 (1971), p. 267, Theorem 1 (with the sentence opening Subsection 2, p. 266)

import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_Phi
import Definitions.Def_VapnikChervonenkis_Shared_index
import Definitions.Def_VapnikChervonenkis_Shared_growthFunction

namespace VapnikChervonenkis.GrowthFunction

/-- **Theorem 1** of Vapnik and Chervonenkis (1971), p. 267: the growth function `m^S(r)` is
either identically equal to `2^r`, or else it is majorized by `r^n + 1`, where `n` is a positive
constant equal to the first value of `r` for which `m^S(r) = 2^r` is violated. The class `S` is
assumed nonempty (for `S = ∅` the first violation is `r = 0`, and `n` is not positive). -/
theorem theorem1_growth_dichotomy {X : Type*} (S : Set (Set X)) (hS : S.Nonempty) :
    (∀ r : ℕ, Shared.growthFunction S r = 2 ^ r) ∨
      ∃ n : ℕ, 0 < n ∧ Shared.growthFunction S n ≠ 2 ^ n ∧
        (∀ r < n, Shared.growthFunction S r = 2 ^ r) ∧
        ∀ r : ℕ, Shared.growthFunction S r ≤ r ^ n + 1 := by sorry

end VapnikChervonenkis.GrowthFunction
