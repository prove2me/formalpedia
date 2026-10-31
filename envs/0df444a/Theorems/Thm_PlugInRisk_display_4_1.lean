-- Prove2me | Theorems.Thm_PlugInRisk_display_4_1
-- name    : PlugInRisk.display_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:27:16.894223+00:00
-- url     : https://prove2.me/theorems/9b8ea31f-9731-4c3e-b13e-a179c4e36a1f
-- title:
--   Spectral (Kusuoka) representation, display (4.1)
-- statement:
--   Let $p\in[1,\infty]$ and let $\rho$ be a convex law-invariant risk measure on $L^p$ of the standard probability space. Then there are a set $\mathcal M$ of probability measures on $[0,1)$ and a penalty $\beta:\mathcal M\to[0,\infty)$ such that
--
--   $$
--   \rho(X)=\sup_{\gamma\in\mathcal M}\Bigl(\int_{[0,1)}\mathrm{AVaR}_u(X)\,\gamma(du)-\beta(\gamma)\Bigr)\qquad\text{for all }X\in L^p,
--   $$
--
--   all integrals being finite; moreover $\mathcal M$ is convex and $\beta$ is a convex function on $\mathcal M$.
--
--   The paper takes this from Jouini–Schachermayer–Touzi, Kusuoka, and Filipović–Svindland (unbounded case); it reduces every law-invariant risk measure to average values at risk, which is how the rates for AVaR transfer to general $\rho$.
--
--   Differences from the source:
--
--   - encoding: 𝓜 a set of probability measures on [0,1) with its Borel σ-field → probability measures on ℝ with γ([0,1)ᶜ) = 0; reason: same objects
--   - encoding: ρ(X) = sup_{γ∈𝓜}(…) → IsLUB of the set of values; u ↦ AVaR_u(X) γ-integrable for γ ∈ 𝓜; reason: each integral is at most ρ(X) + β(γ) < ∞ and AVaR_u(X) ≥ E[X], so finiteness is implied; IsLUB avoids the junk value of a real ⨆
--   - reading: β : 𝓜 → [0, ∞) is a convex function → 𝓜 closed under mixtures tγ₁ + (1−t)γ₂ and β(tγ₁ + (1−t)γ₂) ≤ tβ(γ₁) + (1−t)β(γ₂); reason: convexity of a function presupposes a convex domain
--   - encoding: ρ : Lᵖ → ℝ law-invariant risk measure on a standard probability space → ρ on functions [0,1] → ℝ with IsRiskMeasure p ρ (axioms on MemLp X p); reason: same instances
-- source:
--   Bartl & Tangpi, Non-asymptotic convergence rates for the plug-in estimation of risk measures, arXiv:2003.10479v2, display (4.1), p.17 (citing [30], [21], [39])

import Mathlib
import Definitions.Def_PlugInRisk_IsRiskMeasure
import Definitions.Def_PlugInRisk_avar
import Definitions.Def_PlugInRisk_HasSpectralRep

open MeasureTheory
open scoped ENNReal

namespace PlugInRisk

/-- **Spectral (Kusuoka) representation, display (4.1)** (Bartl & Tangpi, arXiv:2003.10479v2,
display (4.1), p.17, citing [30], [21], [39]): "by [30], every law–invariant risk measure
automatically satisfies the Fatou-property as well as the spectral representation
ρ(X) = sup_{γ∈𝓜} ( ∫_{[0,1)} AVaR_u(X) γ(du) − β(γ) ) for X ∈ Lᵖ. See [21] for the case of
unbounded random variables. Here 𝓜 is a subset of probability measures on [0, 1) armed with its
Borel σ-field, β : 𝓜 → [0, ∞) is a convex function".

For every `p ∈ [1, ∞]` and every convex law-invariant risk measure `ρ` on `Lᵖ` of the standard
probability space there are a set `𝓜` of probability measures on `[0,1)` and a penalty `β ≥ 0`
representing `ρ` on `Lᵖ`, with `𝓜` closed under mixtures and `β` convex on `𝓜`.

**Formalization Note** `p` ranges over `[1, ∞]` (§4, p.17: "ρ : Lᵖ → ℝ with p ∈ [1, ∞]").
Convexity of `β : 𝓜 → [0, ∞)` is stated on a convex `𝓜`: mixtures `t γ₁ + (1−t) γ₂` stay in
`𝓜` and `β` of a mixture is at most the mixture of the values. -/
theorem display_4_1 (p : ℝ≥0∞) (hp : 1 ≤ p) (ρ : (unitInterval → ℝ) → ℝ)
    (hρ : IsRiskMeasure p ρ) :
    ∃ (𝓜 : Set (Measure ℝ)) (β : Measure ℝ → ℝ), HasSpectralRep p ρ 𝓜 β ∧
      ∀ γ₁ ∈ 𝓜, ∀ γ₂ ∈ 𝓜, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        ENNReal.ofReal t • γ₁ + ENNReal.ofReal (1 - t) • γ₂ ∈ 𝓜 ∧
        β (ENNReal.ofReal t • γ₁ + ENNReal.ofReal (1 - t) • γ₂) ≤ t * β γ₁ + (1 - t) * β γ₂ := by sorry

end PlugInRisk
