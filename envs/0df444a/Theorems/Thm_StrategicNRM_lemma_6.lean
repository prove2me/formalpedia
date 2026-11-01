-- Prove2me | Theorems.Thm_StrategicNRM_lemma_6
-- name    : StrategicNRM.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:29:38.211842+00:00
-- url     : https://prove2.me/theorems/e98f0de4-320c-4603-a7a7-768c39c1fd6d
-- title:
--   Lemma 6, p.19 — the virtual-value problem is bounded by the fluid problem
-- statement:
--   Under Assumption 1, for any $\chi\in[0,1]$ and any truncation $B\in[0,\infty]$ of the virtual value,
--
--   $$
--   \tilde J^\chi_B\le\bar J^\chi .
--   $$
--
--   The printed statement is $B=\infty$. The bound turns an infinite-dimensional problem into the finite-dimensional problem (18): under the monotone virtual value, the best use of a given purchase probability for a product is the threshold rule with that probability.
--
--   Differences from the source:
--   - generalization: J̃^χ ≤ J̄^χ → the same for the virtual value truncated at any B ∈ [0,∞]; reason: B = ∞ is the printed statement, and the finite B are what Lemma 4(a) needs
--   - reading: E[Σⱼ b̃ʲ_φ] ≤ χ, ∀ φ → Σⱼ b̃ʲ_φ ≤ χ for every φ; reason: b̃ is a function of φ alone, and the printed proof uses b̃ʲ ≤ χ termwise
--   - reading: Assumption 1: v − F̄ⱼ(v)/fⱼ(v) non-decreasing for all v ≥ 0 → fⱼ > 0 a.e. on the interior of the support, and the virtual value non-decreasing where fⱼ > 0 there; reason: p.18 names the uniform distribution, for which the literal assumption is meaningless
--   - encoding: q ∈ ℝⁿ in (18) → q ∈ [0,∞]ⁿ with ∞ · 0 = 0; reason: a negative price is dominated by 0 and ∞ encodes F̄ⱼ = 0; the suprema agree whenever the real problem is feasible, and with x₀ⁱ = 0 on unbounded support the real problem would be infeasible
--   - encoding: the objective of (12) as an expectation over H_T → λT times the expectation under μ, by Campbell's formula; reason: the two are equal
--   - encoding: (12) over all b̃ with b̃ʲ_φ ∈ [0,1] → b̃ measurable with Σⱼ ψⱼᴮ(vʲ) b̃ʲ integrable under μ; reason: the objective must be defined; for finite B, ψᴮ f is integrable (ψᴮ ≤ B, and ∫ψ⁻ f ≤ ∫₀ᴮ F̄), and at B = ∞ under Assumption 1 or under the hypotheses of (b) every measurable b̃ ∈ [0,1] qualifies
-- source:
--   Chen & Trichakis, On Revenue Management with Strategic Customers Choosing When and What to Buy, SSRN 2959489 (version of May 29, 2018), §3.2.2, Lemma 6, p.19

import Mathlib
import Definitions.Def_StrategicNRM_Virtual

open MeasureTheory
open scoped ENNReal NNReal

namespace StrategicNRM

variable {n m : ℕ}

/-- Chen & Trichakis, SSRN 2959489 (version of May 29, 2018), Lemma 6, p.19: for any `χ ∈ [0,1]`,
`J̃^χ ≤ J̄^χ`, under Assumption 1. It holds for every truncation `B ∈ [0,∞]` of the virtual value;
`B = ∞` is the printed statement. -/
theorem lemma_6 (I : Instance n m) (hA : I.Assumption1) (B : ℝ≥0∞) {χ : ℝ}
    (hχ : χ ∈ Set.Icc (0 : ℝ) 1) : I.Jtilde B χ ≤ I.Jbar χ := by sorry

end StrategicNRM
