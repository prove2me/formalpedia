-- Prove2me | Theorems.Thm_PlugInRisk_lemma_4_4
-- name    : PlugInRisk.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:27:41.566158+00:00
-- url     : https://prove2.me/theorems/fa9f961c-2b49-46ea-9ea7-c9c493489bf9
-- title:
--   Lemma 4.4: penalties can be truncated on $L^p$-balls
-- statement:
--   Let $1<q\le p\le\infty$, let $\rho$ be a $q$-regular convex law-invariant risk measure on $L^p$, and let $(\mathcal M,\beta)$ be a spectral representation (4.1) of $\rho$ on $L^p$. For every $a>0$ there is $b>0$ such that
--
--   $$
--   \rho(X)=\sup_{\gamma\in\mathcal M,\ \beta(\gamma)\le b}\Bigl(\int_{[0,1)}\mathrm{AVaR}_u(X)\,\gamma(du)-\beta(\gamma)\Bigr)
--   $$
--
--   for all $X\in L^p$ with $\|X\|_{L^p}\le a$.
--
--   Only measures with bounded penalty matter on bounded sets, which together with Lemma 4.5 bounds the mass these measures put near $u=1$.
--
--   Differences from the source:
--
--   - generalization: (𝓜, β) the representation (4.1) → every pair with HasSpectralRep p ρ 𝓜 β (convexity not assumed); reason: specializes to the pair of (4.1)
--   - generalization: the hypotheses on F, G, 𝒢 and (a)/(b) of Theorem 4.1 → dropped; reason: they do not occur in the lemma; the source's hypotheses imply the remaining ones
--   - encoding: sup over {γ ∈ 𝓜 : β(γ) ≤ b} → IsLUB; reason: avoids the junk value of a real ⨆; the source asserts the value is ρ(X)
-- source:
--   Bartl & Tangpi, Non-asymptotic convergence rates for the plug-in estimation of risk measures, arXiv:2003.10479v2, Lemma 4.4, p.18

import Mathlib
import Definitions.Def_PlugInRisk_IsRiskMeasure
import Definitions.Def_PlugInRisk_IsQRegular
import Definitions.Def_PlugInRisk_avar
import Definitions.Def_PlugInRisk_HasSpectralRep

open MeasureTheory
open scoped ENNReal

namespace PlugInRisk

/-- **Lemma 4.4** (Bartl & Tangpi, arXiv:2003.10479v2, Lemma 4.4, p.18): "Let the assumptions of
Theorem 4.1 be satisfied. For every fixed a > 0, there exists a constant b > 0 such that
ρ(X) = sup_{γ∈𝓜: s.t. β(γ)≤b} ( ∫_{[0,1)} AVaR_u(X) γ(du) − β(γ) ) for all X ∈ Lᵖ with
‖X‖_{Lᵖ} ≤ a."

Here `1 < q ≤ p ≤ ∞`, `ρ` is a `q`-regular convex law-invariant risk measure on `Lᵖ`, and
`(𝓜, β)` is a spectral representation (4.1) of `ρ` on `Lᵖ`.

**Formalization Note** The statement is made for every representing pair `(𝓜, β)`, in
particular the one of (4.1); the supremum is stated with `IsLUB`. The hypotheses of Theorem 4.1
on `F`, `G`, `𝒢` do not occur in the lemma and are omitted. -/
theorem lemma_4_4 (q : ℝ) (p : ℝ≥0∞) (hq : 1 < q) (hqp : ENNReal.ofReal q ≤ p)
    (ρ : (unitInterval → ℝ) → ℝ) (hρ : IsRiskMeasure p ρ) (hreg : IsQRegular q ρ)
    (𝓜 : Set (Measure ℝ)) (β : Measure ℝ → ℝ) (hrep : HasSpectralRep p ρ 𝓜 β)
    (a : ℝ) (ha : 0 < a) :
    ∃ b : ℝ, 0 < b ∧ ∀ X : unitInterval → ℝ, MemLp X p volume →
      eLpNorm X p volume ≤ ENNReal.ofReal a →
      IsLUB {y : ℝ | ∃ γ ∈ 𝓜, β γ ≤ b ∧ y = ∫ u, avar (volume.map X) u ∂γ - β γ}
        (ρ X) := by sorry

end PlugInRisk
