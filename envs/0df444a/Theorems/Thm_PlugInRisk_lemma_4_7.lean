-- Prove2me | Theorems.Thm_PlugInRisk_lemma_4_7
-- name    : PlugInRisk.lemma_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:26:49.396414+00:00
-- url     : https://prove2.me/theorems/77f6634f-22ef-475c-87f8-162b623ae753
-- title:
--   Lemma 4.7: uniform AVaR estimation error
-- statement:
--   Let $p\in(1,\infty]$, let $F,G_1,\dots,G_e$ be measurable on a Polish space $\mathcal X$ with $J:=1+|F|+\sum_i|G_i|$ in $L^{2p}(\mu)$ if $p<\infty$ and bounded if $p=\infty$, and let $\mathcal G\subset\mathbb R^e$ be countable and bounded. Put
--
--   $$
--   \delta_u^N:=\sup_{g\in\mathcal G}\bigl|\mathrm{AVaR}^\mu_u(F+g\cdot G)-\mathrm{AVaR}^{\mu_N}_u(F+g\cdot G)\bigr|.
--   $$
--
--   Then there is $C>0$ such that for every i.i.d. sample with law $\mu$, every $N\ge1$ and every $v\in(0,1)$
--
--   $$
--   E\Bigl[\sup_{u\in[0,v]}\delta_u^N\Bigr]\le\frac{C}{(1-v)\sqrt N}\wedge\frac{C}{(1-v)^{1/2p}}.
--   $$
--
--   Differences from the source:
--
--   - generalization: the assumptions of Theorem 4.1: 1 < q ≤ p ≤ ∞, ρ q-regular on Lᵖ, (a) ‖w_p(tJᵖ)‖_{L²(μ)} < ∞ if p < ∞, (b) J bounded if p = ∞ → 1 < p, ‖J‖_{L^{2p}(μ)} < ∞ if p < ∞, J bounded if p = ∞; reason: ρ and q do not occur in the lemma, and (a) implies ‖J‖_{L^{2p}(μ)} < ∞ since w_p(x) ≥ ρ(x) = x (p.17)
--   - reading: C generic → C chosen after p, 𝒳, μ, F, G, 𝒢 and before the sample, N and v; reason: the paper's convention for constants (p.11): C may depend on all parameters but not on N
--   - encoding: E[…] → outer expectation outerExp of the supremum in [0, ∞]; reason: the quantity is measurable (p.21), where E* = E
--   - encoding: 𝒢 bounded; 1/2p with 1/∞ = 0 → Bornology.IsBounded 𝒢; (p⁻¹).toReal / 2; reason: boundedness does not depend on the norm; same values
-- source:
--   Bartl & Tangpi, Non-asymptotic convergence rates for the plug-in estimation of risk measures, arXiv:2003.10479v2, Lemma 4.7 and display (4.7), p.21

import Mathlib
import Definitions.Def_PlugInRisk_avar
import Definitions.Def_PlugInRisk_empiricalMeasure
import Definitions.Def_PlugInRisk_IsIIDSample
import Definitions.Def_PlugInRisk_outerExp

open MeasureTheory
open scoped ENNReal

namespace PlugInRisk

/-- **Lemma 4.7** (Bartl & Tangpi, arXiv:2003.10479v2, Lemma 4.7 and display (4.7), p.21): with
`δ_u^N := sup_{g∈𝒢} |AVaR_u^μ(F + g·G) − AVaR_u^{μ_N}(F + g·G)|`, "Let the assumptions of
Theorem 4.1 be satisfied. We have that
E[ sup_{u∈[0,v]} δ_u^N ] ≤ C/((1 − v)√N) ∧ C/(1 − v)^{1/2p} for every v ∈ (0, 1)."

Setting: `p ∈ (1, ∞]`, `F, G₁, …, G_e : 𝒳 → ℝ` measurable, `𝒢 ⊂ ℝᵉ` countable and bounded,
`J := 1 + |F| + Σᵢ|Gᵢ|` with `‖J‖_{L^{2p}(μ)} < ∞` if `p < ∞` and `J` bounded if `p = ∞`.

**Formalization Note** `C` is chosen after the data `p, 𝒳, μ, F, G, 𝒢` and before the sample,
`N` and `v` (the paper's convention for generic constants, p.11: `C` may depend on all
parameters but not on `N`). The expectation is the outer expectation (the quantity is
measurable, p.21, so it equals `E`). `1/(2p)` is `(p⁻¹).toReal / 2`, which is `0` at `p = ∞`. -/
theorem lemma_4_7 (p : ℝ≥0∞) (hp : 1 < p) {e : ℕ}
    (𝒳 : Type) [TopologicalSpace 𝒳] [PolishSpace 𝒳] [MeasurableSpace 𝒳] [BorelSpace 𝒳]
    (μ : Measure 𝒳) [IsProbabilityMeasure μ]
    (F : 𝒳 → ℝ) (hF : Measurable F) (G : Fin e → 𝒳 → ℝ) (hG : ∀ i, Measurable (G i))
    (𝒢 : Set (Fin e → ℝ)) (h𝒢c : 𝒢.Countable) (h𝒢b : Bornology.IsBounded 𝒢)
    (hJp : p ≠ ⊤ → eLpNorm (fun x => 1 + |F x| + ∑ i, |G i x|) (2 * p) μ < ⊤)
    (hJinf : p = ⊤ → ∃ K : ℝ, ∀ x, 1 + |F x| + ∑ i, |G i x| ≤ K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (S : ℕ → Ω → 𝒳), IsIIDSample P S μ → ∀ N : ℕ, 1 ≤ N → ∀ v : ℝ, 0 < v → v < 1 →
        outerExp P (fun ω => ⨆ u ∈ Set.Icc (0 : ℝ) v, ⨆ g ∈ 𝒢,
            ENNReal.ofReal |avar (μ.map (fun x => F x + ∑ i, g i * G i x)) u -
              avar ((empiricalMeasure S N ω).map (fun x => F x + ∑ i, g i * G i x)) u|)
          ≤ ENNReal.ofReal (min (C / ((1 - v) * Real.sqrt N))
              (C / (1 - v) ^ ((p⁻¹).toReal / 2))) := by sorry

end PlugInRisk
