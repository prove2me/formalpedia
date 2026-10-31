-- Prove2me | Theorems.Thm_PlugInRisk_lemma_4_5
-- name    : PlugInRisk.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:27:48.85904+00:00
-- url     : https://prove2.me/theorems/21e8d273-c9de-4c23-8eac-6162d4005101
-- title:
--   Lemma 4.5: $\Gamma_b([r,1))\le C(1-r)^{1/q}$
-- statement:
--   Let $1<q\le p\le\infty$, let $\rho$ be a $q$-regular convex law-invariant risk measure on $L^p$, and let $(\mathcal M,\beta)$ represent $\rho$ as in (4.1). For every $b\ge0$ there is a constant $C$ such that
--
--   $$
--   \Gamma_b([r,1)):=\sup_{\gamma\in\mathcal M,\ \beta(\gamma)\le b}\gamma([r,1))\le C(1-r)^{1/q}\qquad\text{for every }r\in[0,1).
--   $$
--
--   Differences from the source:
--
--   - generalization: (𝓜, β) the representation (4.1) → every pair with HasSpectralRep p ρ 𝓜 β; reason: specializes to the pair of (4.1)
--   - generalization: the hypotheses of Theorem 4.1 on F, G, 𝒢 and (a)/(b) → dropped; reason: they do not occur in the lemma
--   - encoding: sup_{γ: β(γ)≤b} γ([r,1)) ≤ C(1−r)^{1/q} → γ([r,1)) ≤ C(1−r)^{1/q} for each γ ∈ 𝓜 with β(γ) ≤ b; reason: a supremum is at most a bound iff every element is
-- source:
--   Bartl & Tangpi, Non-asymptotic convergence rates for the plug-in estimation of risk measures, arXiv:2003.10479v2, Lemma 4.5, p.20

import Mathlib
import Definitions.Def_PlugInRisk_IsRiskMeasure
import Definitions.Def_PlugInRisk_IsQRegular
import Definitions.Def_PlugInRisk_HasSpectralRep

open MeasureTheory
open scoped ENNReal

namespace PlugInRisk

/-- **Lemma 4.5** (Bartl & Tangpi, arXiv:2003.10479v2, Lemma 4.5, p.20): "Let the assumptions of
Theorem 4.1 be satisfied. For every fixed b ∈ ℝ₊, we have
Γ_b([r, 1)) := sup_{γ∈𝓜 s.t. β(γ)≤b} γ([r, 1)) ≤ C(1 − r)^{1/q} for every r ∈ [0, 1)."

**Formalization Note** `Γ_b([r,1)) ≤ C(1−r)^{1/q}` is stated for each `γ ∈ 𝓜` with
`β(γ) ≤ b` (a supremum is at most a bound iff every element is). The constant `C` depends on `b`
(and `ρ`, `q`, `𝓜`, `β`), not on `r`. The statement is made for every representing pair
`(𝓜, β)` of `ρ` on `Lᵖ`; the hypotheses of Theorem 4.1 on `F`, `G`, `𝒢` do not occur. -/
theorem lemma_4_5 (q : ℝ) (p : ℝ≥0∞) (hq : 1 < q) (hqp : ENNReal.ofReal q ≤ p)
    (ρ : (unitInterval → ℝ) → ℝ) (hρ : IsRiskMeasure p ρ) (hreg : IsQRegular q ρ)
    (𝓜 : Set (Measure ℝ)) (β : Measure ℝ → ℝ) (hrep : HasSpectralRep p ρ 𝓜 β)
    (b : ℝ) (hb : 0 ≤ b) :
    ∃ C : ℝ, ∀ γ ∈ 𝓜, β γ ≤ b → ∀ r : ℝ, 0 ≤ r → r < 1 →
      (γ (Set.Ico r 1)).toReal ≤ C * (1 - r) ^ (1 / q) := by sorry

end PlugInRisk
