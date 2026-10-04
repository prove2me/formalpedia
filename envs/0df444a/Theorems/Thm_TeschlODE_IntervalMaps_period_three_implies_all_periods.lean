-- Prove2me | Theorems.Thm_TeschlODE_IntervalMaps_period_three_implies_all_periods
-- name    : TeschlODE.IntervalMaps.period_three_implies_all_periods
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T18:43:15.399337+00:00
-- url     : https://prove2.me/theorems/85c7c521-647e-4655-8b40-e8b0a61a9cff
-- title:
--   Lemma 11.1 — period three implies all periods for a continuous map of a compact interval
-- statement:
--   Let $I = [a, b] \subseteq \mathbb{R}$ be a compact interval and $f : I \to I$ continuous. Suppose $f$ has an orbit of period three, i.e. a point $x \in I$ of prime period $3$. Then for every $n \in \mathbb{N} = \{1, 2, \dots\}$ there is a point of prime period $n$:
--   $$\exists\, x \in I:\quad f^n(x) = x \ \text{ and } \ f^m(x) \ne x \ \text{ for } 1 \le m < n .$$
--
--   This is the first case of Sarkovskii's theorem (Theorem 11.2), and the only one the book proves.
--
--   **Formalization Note.** $f$ is a continuous self-map of the subtype $[a,b]$; the prime period is Mathlib's `Function.minimalPeriod`. "An orbit of period three" is read as an orbit of prime period three, as in the book's proof (three points $a < b < c$) and its convention (§10.2, p. 282) that the period of a periodic point means its prime period.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 294, Lemma 11.1

import Mathlib

namespace TeschlODE.IntervalMaps

/-- Teschl, Lemma 11.1, p. 294: let `I = [a, b] ⊆ ℝ` be a compact interval and `f : I → I`
continuous. If `f` has an orbit of (prime) period three, then for every `n ∈ ℕ = {1, 2, …}` it
has an orbit of prime period `n`. The prime period is Mathlib's `Function.minimalPeriod`. -/
theorem period_three_implies_all_periods (a b : ℝ) (hab : a ≤ b)
    (f : Set.Icc a b → Set.Icc a b) (hf : Continuous f)
    (h3 : ∃ x : Set.Icc a b, Function.minimalPeriod f x = 3) :
    ∀ n : ℕ, 1 ≤ n → ∃ x : Set.Icc a b, Function.minimalPeriod f x = n := by sorry

end TeschlODE.IntervalMaps
