-- Prove2me | Theorems.Thm_VapnikChervonenkis_GrowthFunction_index_lt_phi_of_growth_ne
-- name    : VapnikChervonenkis.GrowthFunction.index_lt_phi_of_growth_ne
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:36:55.714319+00:00
-- url     : https://prove2.me/theorems/f17d9b4f-19fc-4635-82c3-77662869323c
-- title:
--   If m^S(n) ≠ 2^n then Δ^S(x_1, …, x_r) < Φ(n, r) for every sample of size r > n
-- statement:
--   Let $X$ be a set, $S$ a collection of subsets of $X$, $m^S$ its growth function and $\Phi$ the function defined by the recurrence (1). Suppose that $m^S(r)$ is not identically equal to $2^r$, and let $n$ be the first value of $r$ for which $m^S(r) \ne 2^r$, so that $m^S(n) \ne 2^n$ and $m^S(r) = 2^r$ for every $r < n$. Then for every $r > n$ and every sample $x_1, \dots, x_r$ of size $r$,
--
--   $$
--   \Delta^S(x_1, \dots, x_r) < \Phi(n, r) .
--   $$
--
--   Taking the maximum over samples gives $m^S(r) \le \Phi(n, r)$ for all $r > n$, the combinatorial half of Theorem 1.
--
--   **Formalization Note.** "The first value of $r$" is stated as the two hypotheses $m^S(n) \ne 2^n$ and $m^S(r) = 2^r$ for all $r < n$. No positivity of $n$ is assumed: for $n = 0$ the hypotheses mean $S = \emptyset$, every index is $0$ and $\Phi(0, r) = 1$.
-- source:
--   Vapnik and Chervonenkis, On the Uniform Convergence of Relative Frequencies of Events to Their Probabilities, Theory Probab. Appl. 16 (1971), p. 268, proof of Theorem 1, first display

import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_Phi
import Definitions.Def_VapnikChervonenkis_Shared_index
import Definitions.Def_VapnikChervonenkis_Shared_growthFunction

namespace VapnikChervonenkis.GrowthFunction

/-- Vapnik and Chervonenkis (1971), p. 268, first display of the proof of Theorem 1: suppose
`m^S(r)` is not identically `2^r` and `n` is the first value of `r` for which `m^S(r) ≠ 2^r`
(`m^S(n) ≠ 2^n` and `m^S(r) = 2^r` for all `r < n`). Then for any sample `x_1, ···, x_r` of size
`r > n`, `Δ^S(x_1, ···, x_r) < Φ(n, r)`. -/
theorem index_lt_phi_of_growth_ne {X : Type*} (S : Set (Set X)) (n : ℕ)
    (hn : Shared.growthFunction S n ≠ 2 ^ n)
    (hmin : ∀ r < n, Shared.growthFunction S r = 2 ^ r) (r : ℕ) (hr : n < r) (x : Fin r → X) :
    Shared.index S x < Shared.Phi n r := by sorry

end VapnikChervonenkis.GrowthFunction
