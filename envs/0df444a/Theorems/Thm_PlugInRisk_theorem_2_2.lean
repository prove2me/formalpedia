-- Prove2me | Theorems.Thm_PlugInRisk_theorem_2_2
-- name    : PlugInRisk.theorem_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:27:39.313087+00:00
-- url     : https://prove2.me/theorems/35c8b008-3382-4bdf-9477-db8a3795b1d4
-- title:
--   Theorem 2.2: plug-in rates $C/N^{1/2q}$ and $C\exp(-cN\varepsilon^{2q})$ for $q$-regular risk measures
-- statement:
--   Let $q\in(1,\infty)$ and let $\rho:L^\infty\to\mathbb R$ be a $q$-regular convex law-invariant risk measure on the standard probability space. Let $\mu$ be a probability law on a Polish space $\mathcal X$, $F,G_1,\dots,G_e:\mathcal X\to\mathbb R$ bounded measurable functions, $\mathcal G\subset\mathbb R^e$ a nonempty countable bounded set of strategies, and
--
--   $$
--   \pi^\nu(F)=\inf_{g\in\mathcal G}\rho^\nu\Bigl(F+\sum_{i=1}^eg_iG_i\Bigr).
--   $$
--
--   Let $\mu_N$ be the empirical measure of an i.i.d. sample with law $\mu$. There are constants $c,C>0$, depending only on $\rho$, $q$, the number $e$ of options, a bound $K$ on $|F|$ and $|G_i|$, and a bound $R$ on the Euclidean norm of the strategies, such that:
--
--   1. (moment bound) for all $N\ge1$,
--   $$
--   E^*\bigl[\,|\pi^\mu(F)-\pi^{\mu_N}(F)|\,\bigr]\le\frac{C}{N^{1/2q}};
--   $$
--   2. (deviation inequality) for all $N\ge1$ and $\varepsilon>0$,
--   $$
--   P^*\bigl[\,|\pi^\mu(F)-\pi^{\mu_N}(F)|\ge\varepsilon\,\bigr]\le C\exp\bigl(-cN\varepsilon^{2q}\bigr).
--   $$
--
--   The rates do not depend on the dimension of $\mathcal X$; the plug-in estimator of a hedged risk is therefore consistent at an explicit, dimension-free rate for every $q$-regular risk measure.
--
--   Differences from the source:
--
--   - reading: c, C depend on ρ, the maximal range of F, G, the number of options e and the maximal Euclidean norm in 𝒢 (p.7) → ∃ c C after q, ρ, e, K, R and before 𝒳, μ, F, G, 𝒢, the sample, N and ε; reason: the dependence sentence of p.7 read as uniformity in everything else (the stronger reading)
--   - reading: a standard probability space (Definition 1.1) → [0,1] with Lebesgue measure; reason: the standard atomless probability space; every law on ℝ is realized on it
--   - encoding: 𝒢 ⊂ ℝᵉ countable and bounded (p.6) → 𝒢 countable, nonempty, √(Σ gᵢ²) ≤ R; reason: for 𝒢 = ∅, π = +∞ and the statement is undefined; nonemptiness excludes only that case
--   - encoding: F, G₁, …, G_e bounded → |F x| ≤ K and |G i x| ≤ K for all x, with K a parameter of the constants; reason: same instances
--   - encoding: E*, P* → outerExp (infimum over measurable majorants); P of a possibly non-measurable set (outer measure); reason: same values
--   - encoding: i.i.d. sample (S_n)_{n≤N} on (Ω, 𝓕, P); Polish 𝒳 → S : ℕ → Ω → 𝒳 with IsIIDSample, observations S 0, …, S (N−1); 𝒳, Ω : Type; reason: same instances
--   - encoding: ρ : L∞ → ℝ, ρ^ν, π^ν → IsRiskMeasure ⊤ ρ on functions [0,1] → ℝ; lawRisk; hedgedRisk; reason: same instances
-- source:
--   Bartl & Tangpi, Non-asymptotic convergence rates for the plug-in estimation of risk measures, arXiv:2003.10479v2, Theorem 2.2, p.7

import Mathlib
import Definitions.Def_PlugInRisk_IsRiskMeasure
import Definitions.Def_PlugInRisk_IsQRegular
import Definitions.Def_PlugInRisk_lawRisk
import Definitions.Def_PlugInRisk_hedgedRisk
import Definitions.Def_PlugInRisk_empiricalMeasure
import Definitions.Def_PlugInRisk_IsIIDSample
import Definitions.Def_PlugInRisk_outerExp

open MeasureTheory
open scoped ENNReal

namespace PlugInRisk

/-- **Theorem 2.2, rates for general risk measures** (Bartl & Tangpi, arXiv:2003.10479v2,
Theorem 2.2, p.7): "Let q ∈ (1, ∞) and let ρ: L∞ → ℝ be a q-regular risk measure. Then there are
constants c, C > 0 such that the following hold.
(i) We have the moment bound E*[ |π^μ(F) − π^{μ_N}(F)| ] ≤ C / N^{1/2q} for all N ≥ 1.
(ii) We have the matching deviation inequality
P*[ |π^μ(F) − π^{μ_N}(F)| ≥ ε ] ≤ C exp(−cNε^{2q}) for all N ≥ 1 and all ε > 0."
And (p.7): "The constants c and C depend on ρ, the maximal range of F, G, the number of options e
and the maximal Euclidean norm in 𝒢."

Setting (§2, p.6): `μ` is a probability measure on a Polish space `𝒳`, `μ_N` the empirical
measure of an i.i.d. sample with law `μ` on an abstract probability space `(Ω, P)`; `F` and the
options `G₁, …, G_e` are bounded measurable; `𝒢 ⊂ ℝᵉ` is countable and bounded;
`π^ν(F) = inf_{g∈𝒢} ρ^ν(F + Σᵢ gᵢGᵢ)`.

**Formalization Note** `ρ` is a convex law-invariant risk measure on `L∞` of the standard
probability space `[0,1]` with Lebesgue measure. The constants are chosen after `q, ρ, e`, a
bound `K` on `|F|` and on each `|Gᵢ|`, and a bound `R` on the Euclidean norm of the strategies,
and before `𝒳, μ, F, G, 𝒢`, the sample, `N` and `ε`. `𝒢` is nonempty (for `𝒢 = ∅`, `π = +∞`).
`E*` is `outerExp`; `P*` is `P` applied to a possibly non-measurable set. The sample is
`S 0, …, S (N−1)`. -/
theorem theorem_2_2 (q : ℝ) (hq : 1 < q) (ρ : (unitInterval → ℝ) → ℝ)
    (hρ : IsRiskMeasure ⊤ ρ) (hreg : IsQRegular q ρ) (e : ℕ) (K R : ℝ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (𝒳 : Type) [TopologicalSpace 𝒳] [PolishSpace 𝒳] [MeasurableSpace 𝒳] [BorelSpace 𝒳]
        (μ : Measure 𝒳) [IsProbabilityMeasure μ] (F : 𝒳 → ℝ) (G : Fin e → 𝒳 → ℝ),
        Measurable F → (∀ i, Measurable (G i)) → (∀ x, |F x| ≤ K) → (∀ i x, |G i x| ≤ K) →
        ∀ 𝒢 : Set (Fin e → ℝ), 𝒢.Countable → 𝒢.Nonempty →
          (∀ g ∈ 𝒢, Real.sqrt (∑ i, g i ^ 2) ≤ R) →
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (S : ℕ → Ω → 𝒳), IsIIDSample P S μ → ∀ N : ℕ, 1 ≤ N →
          outerExp P (fun ω => ENNReal.ofReal
              |hedgedRisk ρ μ F G 𝒢 - hedgedRisk ρ (empiricalMeasure S N ω) F G 𝒢|)
              ≤ ENNReal.ofReal (C / (N : ℝ) ^ (1 / (2 * q))) ∧
            ∀ ε : ℝ, 0 < ε →
              P {ω | ε ≤ |hedgedRisk ρ μ F G 𝒢 - hedgedRisk ρ (empiricalMeasure S N ω) F G 𝒢|}
                ≤ ENNReal.ofReal (C * Real.exp (-c * N * ε ^ (2 * q))) := by sorry

end PlugInRisk
