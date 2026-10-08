-- Prove2me | Theorems.Thm_ScenarioApproach_Fast_fast_bound_le_of_N2
-- name    : ScenarioApproach.Fast.fast_bound_le_of_N2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T05:05:37.273007+00:00
-- url     : https://prove2.me/theorems/a8a52b4c-671e-4f5b-bba2-607cb88bf863
-- title:
--   §8.3 — N₂ ≥ (1/ε) ln(1/β) makes the FAST bound (8.5) at most β
-- statement:
--   Let $\varepsilon,\beta\in(0,1)$ and let $d,N_1,N_2$ be natural numbers. If
--
--   $$
--   N_2\ \ge\ \frac1\varepsilon\ln\frac1\beta,
--   $$
--
--   then the right-hand side of the FAST bound (8.5) is at most $\beta$:
--
--   $$
--   (1-\varepsilon)^{N_2}\sum_{i=0}^{d-1}\binom{N_1}{i}\varepsilon^i(1-\varepsilon)^{N_1-i}\ \le\ \beta.
--   $$
--
--   Combined with Theorem 8.5 this gives the sample-size rule of FAST: with $N_1=Kd$ first-stage scenarios and $N_2\ge\frac1\varepsilon\ln\frac1\beta$ detuning scenarios, $\mathbb P^{N_1+N_2}\{V(\nu^*_F,\ell^*_F)>\varepsilon\}\le\beta$, so the total number of scenarios grows additively, $Kd+\frac1\varepsilon\ln\frac1\beta$, rather than multiplicatively in $d$ and $1/\varepsilon$.
--
--   **Formalization Note** The statement holds for every $d$ and $N_1$; the book's choice $N_1=Kd$ plays no role in the inequality. The exponent $N_1-i$ is natural-number subtraction, which only matters for $i>N_1$, where $\binom{N_1}{i}=0$.
-- source:
--   Campi & Garatti, Introduction to the Scenario Approach, SIAM/MOS 2018, DOI 10.1137/1.9781611975444, p. 95, §8.3 (Pros: Reduced sample size requirements)

import Mathlib

namespace ScenarioApproach.Fast

/-- The `N₂` rule of FAST (p. 95): for `ε, β ∈ (0, 1)`, if `N₂ ≥ (1/ε) ln(1/β)` then the
right-hand side of (8.5) is at most `β`, whatever `N₁` and `d`:
`(1-ε)^{N₂} ∑_{i=0}^{d-1} (N₁ choose i) ε^i (1-ε)^{N₁-i} ≤ β`. -/
theorem fast_bound_le_of_N2 (d N₁ N₂ : ℕ) (ε β : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hN₂ : (1 / ε) * Real.log (1 / β) ≤ N₂) :
    (1 - ε) ^ N₂ *
        ∑ i ∈ Finset.range d, (N₁.choose i : ℝ) * ε ^ i * (1 - ε) ^ (N₁ - i) ≤ β := by sorry

end ScenarioApproach.Fast
