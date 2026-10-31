-- Prove2me | Theorems.Thm_PlugInRisk_theorem_A_5
-- name    : PlugInRisk.theorem_A_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:27:20.282521+00:00
-- url     : https://prove2.me/theorems/1690054c-2936-4657-b414-34bb520243eb
-- title:
--   Theorem A.5: deviation inequality for uniformly bounded classes
-- statement:
--   Let $a,b>0$ and $M\in\mathbb R$. There is a constant $C$, depending only on $a,b,M$, such that the following holds. Let $S_1,S_2,\dots$ be i.i.d. with law $\mu$ on a Polish space $\mathcal X$ and let $\mathcal F$ be a class of measurable $\mu$-square integrable functions satisfying Assumption A.3, with $|f|\le M$ for all $f\in\mathcal F$ and
--
--   $$
--   \mathcal N(\mathcal F,\|\cdot\|_\infty,\varepsilon)\le\Bigl(\frac a\varepsilon\Bigr)^b\vee1\qquad\text{for all }\varepsilon>0. \tag{A.2}
--   $$
--
--   Then for all $\varepsilon>0$ and $N\ge1$
--
--   $$
--   P\Bigl[\sup_{f\in\mathcal F}\Bigl|\frac1N\sum_{n\le N}f(S_n)-E[f(S)]\Bigr|\ge\varepsilon\Bigr]\le C\exp\Bigl(-\frac{N\varepsilon^2}{C}\Bigr).
--   $$
--
--   The paper derives it from van der Vaart and Wellner, Theorem 2.14.10.
--
--   Differences from the source:
--
--   - encoding: sup_{f∈ℱ} |…| ≥ ε → ENNReal.ofReal ε ≤ ⨆ f ∈ ℱ, ENNReal.ofReal |…|; reason: same event for ε > 0; the supremum in [0, ∞] has no junk value
--   - encoding: N(ℱ, ‖·‖_∞, ε), |f| ≤ M → internal coveringNumber for the [0, ∞]-valued sup distance; |f x| ≤ M for all x; reason: the paper's covering numbers (p.11) and supremum norm
--   - encoding: sample S_1, …, S_N; 𝒳, Ω → S 0, …, S (N−1) of an i.i.d. sequence; 𝒳, Ω : Type; reason: same instances
-- source:
--   Bartl & Tangpi, Non-asymptotic convergence rates for the plug-in estimation of risk measures, arXiv:2003.10479v2, Theorem A.5, p.35 (from [50, Theorem 2.14.10])

import Mathlib
import Definitions.Def_PlugInRisk_IsIIDSample
import Definitions.Def_PlugInRisk_coveringNumber
import Definitions.Def_PlugInRisk_SatisfiesA3

open MeasureTheory
open scoped ENNReal

namespace PlugInRisk

/-- **Theorem A.5** (Bartl & Tangpi, arXiv:2003.10479v2, Theorem A.5, p.35, from [50,
Theorem 2.14.10]): "Suppose that Assumption A.3 is satisfied, that there is M such that |f| ≤ M
for all f ∈ ℱ, and that (A.2) N(ℱ, ‖·‖_∞, ε) ≤ (a/ε)^b ∨ 1 for all ε > 0, where a, b > 0 are
two constants. Then there is a constant C depending only on a, b, M such that
P[ sup_{f∈ℱ} | (1/N) Σ_{n≤N} f(S_n) − E[f(S)] | ≥ ε ] ≤ C exp(−Nε²/C) for all ε > 0 and
N ≥ 1."

Setting (p.34): `S₁, S₂, …` i.i.d. with law `μ` on a Polish space `𝒳`; `ℱ` a set of measurable,
`μ`-square integrable functions.

**Formalization Note** `C` is chosen after `a, b, M` and before everything else. `‖·‖_∞` is the
supremum over `𝒳`, the covering number internal (`coveringNumber`). The supremum over `ℱ` is
taken in `[0, ∞]`; the event is `{ε ≤ sup}` (a measurable event under A.3, p.34; Lean's `P` of
any set is the outer measure). The sample is `S 0, …, S (N−1)`. -/
theorem theorem_A_5 (a b M : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (𝒳 : Type) [TopologicalSpace 𝒳] [PolishSpace 𝒳] [MeasurableSpace 𝒳] [BorelSpace 𝒳]
      (μ : Measure 𝒳) [IsProbabilityMeasure μ] (ℱ : Set (𝒳 → ℝ)),
      (∀ f ∈ ℱ, Measurable f ∧ MemLp f 2 μ) → SatisfiesA3 μ ℱ →
      (∀ f ∈ ℱ, ∀ x, |f x| ≤ M) →
      (∀ ε : ℝ, 0 < ε →
        (coveringNumber (fun h h' : 𝒳 → ℝ => ⨆ x, edist (h x) (h' x)) ℱ (ENNReal.ofReal ε) :
          ℝ≥0∞) ≤ ENNReal.ofReal (max ((a / ε) ^ b) 1)) →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (S : ℕ → Ω → 𝒳), IsIIDSample P S μ → ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, 1 ≤ N →
        P {ω | ENNReal.ofReal ε ≤ ⨆ f ∈ ℱ,
            ENNReal.ofReal |(N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, f (S n ω) - ∫ x, f x ∂μ|}
          ≤ ENNReal.ofReal (C * Real.exp (-((N : ℝ) * ε ^ 2) / C)) := by sorry

end PlugInRisk
