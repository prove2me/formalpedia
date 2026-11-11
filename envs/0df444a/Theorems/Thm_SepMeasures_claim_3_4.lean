-- Prove2me | Theorems.Thm_SepMeasures_claim_3_4
-- name    : SepMeasures.claim_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:09:31.348401+00:00
-- url     : https://prove2.me/theorems/34cde9b9-ba87-49e9-a079-32d9224fa39c
-- title:
--   Claim 3.4 — $|\mathbb E[W]|+|\mathbb E[UW]|\le1$ for a fair sign $U$ and $W\in[-1,1]$
-- statement:
--   Let $U$ be a random variable taking each of the values $-1$ and $+1$ with probability $1/2$, and let $W$ be a random variable with values in $[-1,1]$ (on the same probability space; $U$ and $W$ need not be independent). Then
--   $$|\mathbb E[W]|+|\mathbb E[UW]|\le1.$$
--
--   In the proof of Theorem 3.3 it yields the six inequalities (A)–(F) between the sign correlations $p_i,q_i$.
--
--   Differences from the source:
--   - encoding: random variables U, W; W supported on [−1, 1]; U takes each value in {−1, +1} with probability 1/2 → measurable U W : Ω → ℝ on a probability space (Ω, ℙ); W ∈ [−1, 1] ℙ-almost surely; ℙ{U = 1} = ℙ{U = −1} = 1/2; reason: the standard encoding of random variables; the two probabilities force U ∈ {−1, +1} almost surely
-- source:
--   Correa–Griesbach–Harb–Hommelsheim–Jlibene–Livanos–Solan, Separating Measures by Hyperplanes (manuscript, STOC 2027 submission, sha256 96a8692407ff1815980863f3baa9c5d7b90ba27e781ed19063306f67d26fa82f), Claim 3.4, p.22

import Mathlib

open MeasureTheory

namespace SepMeasures

/-- Correa–Griesbach–Harb–Hommelsheim–Jlibene–Livanos–Solan, *Separating Measures by Hyperplanes*
(manuscript, sha256 96a86924…fa82f), Claim 3.4, p.22: let `U` be a random variable taking
each value in `{−1, +1}` with probability `1/2`, and let `W` be a random variable supported on
`[−1, 1]`. Then `|E[W]| + |E[UW]| ≤ 1`.

**Formalization Note.** `U` and `W` are measurable real functions on a probability space
`(Ω, ℙ)`; they need not be independent. "Supported on `[−1, 1]`" is `W ∈ [−1, 1]` almost
surely. -/
theorem claim_3_4 {Ω : Type*} [MeasurableSpace Ω] (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
    (U W : Ω → ℝ) (hU : Measurable U) (hW : Measurable W)
    (hU1 : ℙ {ω | U ω = 1} = 1 / 2) (hUm1 : ℙ {ω | U ω = -1} = 1 / 2)
    (hWb : ∀ᵐ ω ∂ℙ, W ω ∈ Set.Icc (-1 : ℝ) 1) :
    |∫ ω, W ω ∂ℙ| + |∫ ω, U ω * W ω ∂ℙ| ≤ 1 := by sorry

end SepMeasures
