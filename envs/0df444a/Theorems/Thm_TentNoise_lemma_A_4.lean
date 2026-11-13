-- Prove2me | Theorems.Thm_TentNoise_lemma_A_4
-- name    : TentNoise.lemma_A_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:40:13.307493+00:00
-- url     : https://prove2.me/theorems/c8de8bc4-d4dc-4356-9ebd-416f14100909
-- title:
--   Lemma A.4 — Gaussian sum bounds
-- statement:
--   For every $\alpha>0$,
--
--   $$
--   \sum_{n=1}^\infty e^{-\alpha n^2}\le\frac{\sqrt\pi}{2\sqrt\alpha},\qquad \sum_{n=1}^\infty n\,e^{-\alpha n^2}\le\frac1\alpha .
--   $$
--
--   These are the tail estimates for the spectral series of the reflected heat kernel used in Lemmas A.5 and A.6.
--
--   **Formalization Note** The summation index $n\ge1$ is written $n+1$ with $n\in\mathbb N$. Both series are also asserted to be summable.
--
--   Differences from the source:
--   - encoding: ∑_{n=1}^∞ a_n ≤ B → Summable (n ↦ a_{n+1}) ∧ ∑' n : ℕ, a_{n+1} ≤ B; reason: index shift; summability is asserted so that Lean's default value 0 of a divergent tsum cannot satisfy the bound
-- source:
--   Huan, Risteski, Wei, Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling, STOC 2027 submission (manuscript sha256 67925b3e946da20fbfc5ba5a928c6f5743bf4b2ee96e526e8e738f0494f558e6), Lemma A.4, p.18 (PDF p.18), eqs. (26)–(27)

import Mathlib

open Set

namespace TentNoise

/-- **Lemma A.4 (Gaussian sum bounds)** (Huan, Risteski, Wei, *Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling*, STOC 2027 submission (manuscript sha256 67925b3e…), Lemma A.4, p.18, eqs. (26)–(27)): for every
`α > 0`, `∑_{n≥1} e^{−αn²} ≤ √π/(2√α)` and `∑_{n≥1} n e^{−αn²} ≤ 1/α`.

**Formalization Note** The index `n ≥ 1` is written `n + 1` with `n : ℕ`. Both series are asserted to
be summable, so the bounds are not about Lean's default value `0` of a divergent `tsum`. -/
theorem lemma_A_4 (α : ℝ) (hα : 0 < α) :
    (Summable (fun n : ℕ => Real.exp (-α * ((n : ℝ) + 1) ^ 2)) ∧
      ∑' n : ℕ, Real.exp (-α * ((n : ℝ) + 1) ^ 2) ≤ Real.sqrt Real.pi / (2 * Real.sqrt α)) ∧
    (Summable (fun n : ℕ => ((n : ℝ) + 1) * Real.exp (-α * ((n : ℝ) + 1) ^ 2)) ∧
      ∑' n : ℕ, ((n : ℝ) + 1) * Real.exp (-α * ((n : ℝ) + 1) ^ 2) ≤ 1 / α) := by sorry

end TentNoise
