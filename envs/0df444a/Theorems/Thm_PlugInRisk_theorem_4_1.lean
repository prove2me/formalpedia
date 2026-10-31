-- Prove2me | Theorems.Thm_PlugInRisk_theorem_4_1
-- name    : PlugInRisk.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:27:53.210224+00:00
-- url     : https://prove2.me/theorems/e7bb071d-60d2-4c96-b1cf-2d8f954475a8
-- title:
--   Theorem 4.1: mean error rate $C/N^{(1/q-1/2p)/(2-1/p)}$ on $L^p$
-- statement:
--   Let $1<q\le p\le\infty$ and let $\rho:L^p\to\mathbb R$ be a $q$-regular convex law-invariant risk measure. Let $F,G_1,\dots,G_e$ be measurable on a Polish space $\mathcal X$ with law $\mu$, $J:=1+|F|+\sum_i|G_i|$, and $\mathcal G\subset\mathbb R^e$ countable and bounded. Assume
--
--   1. $\|w_p(tJ^p)\|_{L^2(\mu)}<\infty$ for every $t\ge0$ if $p<\infty$;
--   2. $J$ is bounded if $p=\infty$.
--
--   Then there is $C>0$ such that for every i.i.d. sample with law $\mu$ and every $N\ge1$
--
--   $$
--   E^*\Bigl[\sup_{g\in\mathcal G}\bigl|\rho^\mu(F+g\cdot G)-\rho^{\mu_N}(F+g\cdot G)\bigr|\Bigr]\le\frac{C}{N^{(1/q-1/2p)/(2-1/p)}}.
--   $$
--
--   At $p=\infty$ the exponent is $1/(2q)$; this is the generalization of part (i) of Theorem 2.2 to unbounded data.
--
--   Differences from the source:
--
--   - reading: E[…] → outer expectation outerExp; reason: the quantity need not be measurable; the proof (p.24) works with E*
--   - reading: C generic → C chosen after q, p, ρ, 𝒳, μ, F, G, 𝒢 and before the sample and N; reason: the paper's convention for constants (p.11): C may depend on all parameters but not on N
--   - encoding: ‖w_p(tJᵖ)‖_{L²(μ)} < ∞ → ∫⁻ w_p(t J(x)^p)² μ(dx) < ∞ with w_p in [0, ∞]; reason: same condition
--   - encoding: 𝒢 bounded (and countable, p.6); 1/p with 1/∞ = 0 → Bornology.IsBounded 𝒢, 𝒢.Countable; (p⁻¹).toReal; reason: same instances and values
--   - encoding: ρ : Lᵖ → ℝ, ρ^ν(H) → IsRiskMeasure p ρ on functions [0,1] → ℝ; lawRisk ρ (ν.map H); reason: same instances
-- source:
--   Bartl & Tangpi, Non-asymptotic convergence rates for the plug-in estimation of risk measures, arXiv:2003.10479v2, Theorem 4.1, p.17

import Mathlib
import Definitions.Def_PlugInRisk_IsRiskMeasure
import Definitions.Def_PlugInRisk_IsQRegular
import Definitions.Def_PlugInRisk_lawRisk
import Definitions.Def_PlugInRisk_empiricalMeasure
import Definitions.Def_PlugInRisk_IsIIDSample
import Definitions.Def_PlugInRisk_outerExp
import Definitions.Def_PlugInRisk_wp

open MeasureTheory
open scoped ENNReal

namespace PlugInRisk

/-- **Theorem 4.1** (Bartl & Tangpi, arXiv:2003.10479v2, Theorem 4.1, p.17): "Let
1 < q ≤ p ≤ ∞ and let ρ: Lᵖ → ℝ be a law–invariant risk measure which is q-regular. Assume that
𝒢 is bounded and that
(a) ‖w_p(tJᵖ)‖_{L²(μ)} < ∞ for every t ≥ 0 in case that p < ∞,
(b) J is bounded in case that p = ∞.
Then E[ sup_{g∈𝒢} |ρ^μ(F + g·G) − ρ^{μ_N}(F + g·G)| ] ≤ C / N^{(1/q−1/2p)/(2−1/p)} for all
N ≥ 1."

Here `J := 1 + |F| + Σᵢ|Gᵢ|` ((3.1), p.12), `w_p(x) = sup{ρ(X) : ‖X‖_{Lᵖ} ≤ x}` (p.17), and
`𝒢` is countable (standing assumption, p.6).

**Formalization Note** `C` is chosen after `q, p, ρ, 𝒳, μ, F, G, 𝒢` and before the sample and
`N` (the paper's convention for generic constants, p.11). The expectation is the outer
expectation (the proof, p.24, works with `E*`). `ρ^ν(H) = lawRisk ρ (ν.map H)`. The exponent uses
`1/p = (p⁻¹).toReal` (`0` at `p = ∞`, where it equals `1/(2q)`, Table 1, p.18). Condition (a) is
`∫ w_p(t J(x)^p)² μ(dx) < ∞`. -/
theorem theorem_4_1 (q : ℝ) (p : ℝ≥0∞) (hq : 1 < q) (hqp : ENNReal.ofReal q ≤ p)
    (ρ : (unitInterval → ℝ) → ℝ) (hρ : IsRiskMeasure p ρ) (hreg : IsQRegular q ρ) {e : ℕ}
    (𝒳 : Type) [TopologicalSpace 𝒳] [PolishSpace 𝒳] [MeasurableSpace 𝒳] [BorelSpace 𝒳]
    (μ : Measure 𝒳) [IsProbabilityMeasure μ]
    (F : 𝒳 → ℝ) (hF : Measurable F) (G : Fin e → 𝒳 → ℝ) (hG : ∀ i, Measurable (G i))
    (𝒢 : Set (Fin e → ℝ)) (h𝒢c : 𝒢.Countable) (h𝒢b : Bornology.IsBounded 𝒢)
    (ha : p ≠ ⊤ → ∀ t : ℝ, 0 ≤ t →
      ∫⁻ x, wp p ρ (t * (1 + |F x| + ∑ i, |G i x|) ^ p.toReal) ^ 2 ∂μ < ⊤)
    (hb : p = ⊤ → ∃ K : ℝ, ∀ x, 1 + |F x| + ∑ i, |G i x| ≤ K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (S : ℕ → Ω → 𝒳), IsIIDSample P S μ → ∀ N : ℕ, 1 ≤ N →
        outerExp P (fun ω => ⨆ g ∈ 𝒢,
            ENNReal.ofReal |lawRisk ρ (μ.map (fun x => F x + ∑ i, g i * G i x)) -
              lawRisk ρ ((empiricalMeasure S N ω).map (fun x => F x + ∑ i, g i * G i x))|)
          ≤ ENNReal.ofReal (C / (N : ℝ) ^
              ((1 / q - (p⁻¹).toReal / 2) / (2 - (p⁻¹).toReal))) := by sorry

end PlugInRisk
