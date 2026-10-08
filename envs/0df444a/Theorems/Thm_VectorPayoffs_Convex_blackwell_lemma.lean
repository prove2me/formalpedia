-- Prove2me | Theorems.Thm_VectorPayoffs_Convex_blackwell_lemma
-- name    : VectorPayoffs.Convex.blackwell_lemma
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:07:37.679027+00:00
-- url     : https://prove2.me/theorems/32ad12ae-0199-4dc8-8ec6-a95dab1cd4fb
-- title:
--   LEMMA — a sequence satisfying (5), (6), (7) tends to 0 at a rate depending only on a, b, c
-- statement:
--   Let $a,b,c\in\mathbb R$ and $\varepsilon>0$. There is an integer $N_0$, depending only on $\varepsilon,a,b,c$, such that for every probability space and every sequence of measurable real random variables $\delta_1,\delta_2,\dots$ satisfying conditions (5), (6) and (7),
--   $$\mathrm{Prob}\{\delta_n\ge\varepsilon\text{ for some }n\ge N_0\}<\varepsilon .$$
--
--   Here (5) is $E(\delta_n\mid\delta_1,\dots,\delta_{n-1})\le(1-2/n)\delta_{n-1}+c/n^2$ whenever $\delta_{n-1}>0$ ($n\ge2$), (6) is $0\le\delta_n\le a$ ($n\ge1$), and (7) is $|\delta_n-\delta_{n-1}|\le b/n$ ($n\ge2$).
--
--   This is the probabilistic core of THEOREM 1: once the squared distance of the average payoff from $S$ is shown to satisfy (5)–(7) with constants independent of the opponent's strategy, the uniform rate yields approachability.
--
--   **Formalization Note** The order of quantifiers is the paper's "an $N_0$ depending only on $\varepsilon,a,b,c$ such that for any $\{\delta_n\}$": $N_0$ is chosen before the probability space (any space in `Type`) and the sequence. Conditions (6) and (7) are assumed only almost surely, which makes the statement stronger than a pointwise reading.
-- source:
--   Blackwell, An analog of the minimax theorem for vector payoffs, Pacific J. Math. 6(1), 1956, p. 4, LEMMA (with displays (5), (6), (7) on the same page)

import Mathlib
import Definitions.Def_VectorPayoffs_Convex_Recursion

open MeasureTheory

namespace VectorPayoffs.Convex

/-- Blackwell (1956), §2, p. 4, LEMMA: a sequence satisfying (5), (6), (7) tends to `0` with
probability `1` at a rate depending only on `a, b, c`: `N₀` is chosen before the probability
space and the sequence. -/
theorem blackwell_lemma (a b c ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (δ : ℕ → Ω → ℝ), (∀ n, 1 ≤ n → Measurable (δ n)) → SatisfiesRecursion a b c μ δ →
        (μ {ω | ∃ n, N₀ ≤ n ∧ 1 ≤ n ∧ ε ≤ δ n ω}).toReal < ε := by sorry

end VectorPayoffs.Convex
