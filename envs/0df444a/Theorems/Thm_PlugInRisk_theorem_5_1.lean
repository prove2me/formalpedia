-- Prove2me | Theorems.Thm_PlugInRisk_theorem_5_1
-- name    : PlugInRisk.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:27:38.215567+00:00
-- url     : https://prove2.me/theorems/76013814-82a9-446c-9671-92c0fcca79a6
-- title:
--   Theorem 5.1: deviation inequality $C\exp(-cN\varepsilon^{2q})$, uniform over strategies
-- statement:
--   Let $q\in(1,\infty)$ and let $\rho$ be a $q$-regular convex law-invariant risk measure on $L^\infty$. Let $F,G_1,\dots,G_e$ be bounded measurable functions on a Polish space $\mathcal X$ with law $\mu$ and $\mathcal G\subset\mathbb R^e$ countable and bounded. There are constants $c,C>0$ such that for every i.i.d. sample with law $\mu$, every $\varepsilon>0$ and every $N\ge1$
--
--   $$
--   P^*\Bigl[\sup_{g\in\mathcal G}\bigl|\rho^\mu(F+g\cdot G)-\rho^{\mu_N}(F+g\cdot G)\bigr|\ge\varepsilon\Bigr]\le C\exp\bigl(-cN\varepsilon^{2q}\bigr).
--   $$
--
--   The constants depend only on $\rho$, $q$, $e$, the bound on $|F|$ and $|G_i|$ and the bound on the Euclidean norm of the strategies. Since $|\inf_g a_g-\inf_g b_g|\le\sup_g|a_g-b_g|$, it implies part (ii) of Theorem 2.2.
--
--   Differences from the source:
--
--   - reading: constants c, C > 0 (generic) → c, C chosen after q, ρ, e, K, R and before 𝒳, μ, F, G, 𝒢, the sample, ε and N; reason: §5 proves this as the generalization of Theorem 2.2(ii), whose constants depend only on ρ, the range of F, G, e and the norm bound of 𝒢 (p.7)
--   - reading: ρ^μ(F + g·𝒢) − ρ^{μ_N}(F + g·𝒢) → g·G; reason: g·𝒢 is not well-formed; the proof (p.26) uses g·G
--   - encoding: F and G bounded, 𝒢 bounded (and countable, p.6) → |F| ≤ K, |G i| ≤ K, √(Σ gᵢ²) ≤ R, 𝒢 countable; reason: same instances; K, R are the parameters the constants depend on
--   - encoding: P*[sup ≥ ε] → P of {ω | ofReal ε ≤ ⨆ g ∈ 𝒢, ofReal |…|}; reason: Lean's measure of an arbitrary set is the outer measure
--   - encoding: ρ : L∞ → ℝ, ρ^ν(H) → IsRiskMeasure ⊤ ρ on functions [0,1] → ℝ; lawRisk ρ (ν.map H); reason: same instances
-- source:
--   Bartl & Tangpi, Non-asymptotic convergence rates for the plug-in estimation of risk measures, arXiv:2003.10479v2, Theorem 5.1, p.25

import Mathlib
import Definitions.Def_PlugInRisk_IsRiskMeasure
import Definitions.Def_PlugInRisk_IsQRegular
import Definitions.Def_PlugInRisk_lawRisk
import Definitions.Def_PlugInRisk_empiricalMeasure
import Definitions.Def_PlugInRisk_IsIIDSample

open MeasureTheory
open scoped ENNReal

namespace PlugInRisk

/-- **Theorem 5.1** (Bartl & Tangpi, arXiv:2003.10479v2, Theorem 5.1, p.25): "Assume that F and G
are bounded functions and that the set 𝒢 is bounded. Moreover, let q ∈ (1, ∞) and assume that ρ
is q-regular. Then there are constants c, C > 0 such that
P*[ sup_{g∈𝒢} |ρ^μ(F + g·G) − ρ^{μ_N}(F + g·G)| ≥ ε ] ≤ C exp(−cNε^{2q}) for all ε > 0 and
N ≥ 1."

**Formalization Note** `ρ` is a convex law-invariant risk measure on `L∞` of `[0,1]`. The
constants `c, C` are chosen after `q, ρ, e`, a bound `K` on `|F|` and `|Gᵢ|` and a bound `R` on
the Euclidean norm of the strategies in `𝒢`, and before `𝒳, μ, F, G, 𝒢`, the sample, `ε` and
`N` (the dependence stated for Theorem 2.2, p.7, of which §5 proves this generalization of part
(ii)). The printed `g·𝒢` is read as `g·G`. `𝒢` is countable (standing assumption, p.6). The
supremum is taken in `[0, ∞]`; `P` of a set is its outer measure `P*`. -/
theorem theorem_5_1 (q : ℝ) (hq : 1 < q) (ρ : (unitInterval → ℝ) → ℝ)
    (hρ : IsRiskMeasure ⊤ ρ) (hreg : IsQRegular q ρ) (e : ℕ) (K R : ℝ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (𝒳 : Type) [TopologicalSpace 𝒳] [PolishSpace 𝒳] [MeasurableSpace 𝒳] [BorelSpace 𝒳]
        (μ : Measure 𝒳) [IsProbabilityMeasure μ] (F : 𝒳 → ℝ) (G : Fin e → 𝒳 → ℝ),
        Measurable F → (∀ i, Measurable (G i)) → (∀ x, |F x| ≤ K) → (∀ i x, |G i x| ≤ K) →
        ∀ 𝒢 : Set (Fin e → ℝ), 𝒢.Countable → (∀ g ∈ 𝒢, Real.sqrt (∑ i, g i ^ 2) ≤ R) →
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (S : ℕ → Ω → 𝒳), IsIIDSample P S μ → ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, 1 ≤ N →
          P {ω | ENNReal.ofReal ε ≤ ⨆ g ∈ 𝒢,
              ENNReal.ofReal |lawRisk ρ (μ.map (fun x => F x + ∑ i, g i * G i x)) -
                lawRisk ρ ((empiricalMeasure S N ω).map (fun x => F x + ∑ i, g i * G i x))|}
            ≤ ENNReal.ofReal (C * Real.exp (-c * N * ε ^ (2 * q))) := by sorry

end PlugInRisk
