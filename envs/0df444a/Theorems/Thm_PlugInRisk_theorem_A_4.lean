-- Prove2me | Theorems.Thm_PlugInRisk_theorem_A_4
-- name    : PlugInRisk.theorem_A_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:27:02.441982+00:00
-- url     : https://prove2.me/theorems/7351b628-8cb8-4608-a619-a5f8fa7752cd
-- title:
--   Theorem A.4: Dudley's entropy integral bound for empirical processes
-- statement:
--   Let $S,S_1,S_2,\dots$ be i.i.d. with law $\mu$ on a Polish space $\mathcal X$, $\mu_N$ the empirical measure, and $\mathcal F$ a class of measurable $\mu$-square integrable functions satisfying Assumption A.3. There is an absolute constant $C$ such that for every $f^*\in\mathcal F$ and every $N\ge1$
--
--   $$
--   E\Bigl[\sup_{f\in\mathcal F}\Bigl|\frac1N\sum_{n\le N}f(S_n)-E[f(S)]\Bigr|\Bigr]
--   \le\frac{C}{\sqrt N}\Bigl(E[f^*(S)^2]^{1/2}+E\Bigl[\int_0^\infty\sqrt{\log\mathcal N(\mathcal F,\|\cdot\|_{L^2(\mu_N)},\varepsilon)}\,d\varepsilon\Bigr]\Bigr).
--   $$
--
--   Differences from the source:
--
--   - reading: E[∫₀^∞ √(log N(ℱ, ‖·‖_{L²(μ_N)}, ε)) dε] (measurability not discussed) → outer expectation outerExp; reason: the paper's convention for possibly non-measurable quantities (p.4)
--   - encoding: E[sup_{f∈ℱ} |…|] → outerExp of the supremum in [0, ∞]; reason: the supremum is measurable under A.3 (p.34), where E* = E
--   - encoding: covering numbers and √log → internal coveringNumber in ℕ∞ for the pseudo-distance eLpNorm (f − h) 2 μ_N; sqrtLog = ∞ at ∞; reason: same values; ℱ ∋ f* is nonempty so N ≥ 1
--   - encoding: sample S_1, …, S_N; 𝒳, Ω → S 0, …, S (N−1) of an i.i.d. sequence; 𝒳, Ω : Type; reason: same instances
-- source:
--   Bartl & Tangpi, Non-asymptotic convergence rates for the plug-in estimation of risk measures, arXiv:2003.10479v2, Theorem A.4, p.34

import Mathlib
import Definitions.Def_PlugInRisk_empiricalMeasure
import Definitions.Def_PlugInRisk_IsIIDSample
import Definitions.Def_PlugInRisk_outerExp
import Definitions.Def_PlugInRisk_coveringNumber
import Definitions.Def_PlugInRisk_SatisfiesA3

open MeasureTheory
open scoped ENNReal

namespace PlugInRisk

/-- **Theorem A.4, Dudley's entropy integral theorem, empirical-process version** (Bartl &
Tangpi, arXiv:2003.10479v2, Theorem A.4, p.34): "Suppose that Assumption A.3 is satisfied and let
f* ∈ ℱ be an arbitrary but fixed function in ℱ. Then we have that
E[ sup_{f∈ℱ} | (1/N) Σ_{n≤N} f(S_n) − E[f(S)] | ]
≤ (C/√N) ( E[f*(S)²]^{1/2} + E[ ∫_0^∞ √(log N(ℱ, ‖·‖_{L²(μ_N)}, ε)) dε ] )
for all N ≥ 1, where C is an absolute constant."

Setting (p.34): `S, S₁, S₂, …` are i.i.d. with law `μ` on a Polish space `𝒳`, `μ_N` is the
empirical measure, and `ℱ` is a set of measurable, `μ`-square integrable functions.

**Formalization Note** `C` is chosen before everything else (absolute). Expectations of
possibly non-measurable quantities are outer expectations `outerExp` (the left side is
measurable under Assumption A.3, p.34, so there `E* = E`). The covering numbers are internal,
for the `L²(μ_N)` pseudo-distance `eLpNorm (f − h) 2 μ_N`, and `sqrtLog` is `√(log ·)` with
value `∞` at `N = ∞`. The sample is `S 0, …, S (N−1)`. -/
theorem theorem_A_4 :
    ∃ C : ℝ, 0 < C ∧
    ∀ (𝒳 : Type) [TopologicalSpace 𝒳] [PolishSpace 𝒳] [MeasurableSpace 𝒳] [BorelSpace 𝒳]
      (μ : Measure 𝒳) [IsProbabilityMeasure μ] (ℱ : Set (𝒳 → ℝ)),
      (∀ f ∈ ℱ, Measurable f ∧ MemLp f 2 μ) → SatisfiesA3 μ ℱ →
      ∀ fstar ∈ ℱ,
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (S : ℕ → Ω → 𝒳), IsIIDSample P S μ → ∀ N : ℕ, 1 ≤ N →
        outerExp P (fun ω => ⨆ f ∈ ℱ,
            ENNReal.ofReal |(N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, f (S n ω) - ∫ x, f x ∂μ|)
          ≤ ENNReal.ofReal (C / Real.sqrt N) *
            ((∫⁻ x, ‖fstar x‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ) +
              outerExp P (fun ω => ∫⁻ ε in Set.Ioi (0 : ℝ),
                sqrtLog (coveringNumber
                  (fun f h : 𝒳 → ℝ => eLpNorm (f - h) 2 (empiricalMeasure S N ω)) ℱ
                  (ENNReal.ofReal ε)))) := by sorry

end PlugInRisk
