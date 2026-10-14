-- Prove2me | Theorems.Thm_ReflectedRWLDP_SamplePath_lemma_4_5
-- name    : ReflectedRWLDP.SamplePath.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:36:21.142462+00:00
-- url     : https://prove2.me/theorems/4728b735-6ce7-4639-b506-b95955d81f1e
-- title:
--   Lemma 4.5 — $\Phi_T$ is uniformly continuous in $M_1'$ on the level sets of $I^{\mathbb{BV}[0,T]}_0$
-- statement:
--   Under the standing assumptions (i.i.d. increments with mean $\mu<0$, Assumptions 2.1–2.3, $p>0$), fix $T>0$. Let $\Phi_T(\xi)=\int_0^T(\Psi(\xi)(s))^p\,ds$ on $\mathbb D[0,T]$, and let
--   $$I^{\mathbb{BV}[0,T]}_0(\xi)=\int_0^T\Lambda^*(\dot\xi^{(a)}(s))\,ds+\theta_+\xi^{(u)}(T)+\theta_-\xi^{(d)}(T)$$
--   if $\xi\in\mathbb{BV}[0,T]$ and $\xi(0)=0$, and $\infty$ otherwise. For each $\gamma\ge0$, $\Phi_T$ is uniformly continuous on $\{\xi: I^{\mathbb{BV}[0,T]}_0(\xi)\le\gamma\}$ with respect to $d_{M_1'}$: for every $\varepsilon>0$ there is $\delta>0$ such that
--   $$d_{M_1'}(\xi,\zeta)<\delta\implies|\Phi_T(\xi)-\Phi_T(\zeta)|<\varepsilon$$
--   for all $\xi,\zeta$ in the level set.
--
--   The area functional is not continuous on all of $\mathbb D[0,T]$; this lemma supplies the continuity on level sets needed to transfer a large deviation upper bound to $\Phi_T$.
--
--   **Formalization Note** On p. 22 the downward singular term is printed $\theta_-|\xi^{(d)}(T)|$, which is $\le0$ since $\theta_-<0$. It is a typo for $\theta_-\xi^{(d)}(T)\ge0$, the cost used on pp. 6 and 19, and the formalization uses that nonnegative cost.
-- source:
--   Bazhba, Blanchet, Rhee & Zwart, Sample-Path Large Deviations for Unbounded Additive Functionals of the Reflected Random Walk, arXiv:2003.14381v3, p. 22, Lemma 4.5 (with I^{𝔹𝕍[0,T]}_0 as on p. 19)

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_LargeDeviation
import Definitions.Def_MFGLimit_LDP_LDP
import Definitions.Def_ReflectedRWLDP_SamplePath_PathSpace
import Definitions.Def_ReflectedRWLDP_SamplePath_LDP
import Definitions.Def_ReflectedRWLDP_SamplePath_Model
import Definitions.Def_ReflectedRWLDP_SamplePath_RateFunction

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace ReflectedRWLDP.SamplePath

/-- **Lemma 4.5** (p. 22). For `T > 0` and `γ ≥ 0`, `Φ_T` is uniformly continuous on
`{ξ ∈ 𝔻[0,T] : I^{𝔹𝕍[0,T]}_0(ξ) ≤ γ}` with respect to `d_{M₁′}`. -/
theorem lemma_4_5 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (U : ℕ → Ω → ℝ) (p : ℝ)
    (h : Standing P U p) (T : ℝ) (hT : 0 < T) (γ : ℝ) (hγ : 0 ≤ γ) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ ξ ∈ {ξ : DPath T | rateIT P U T 0 ξ ≤ ENNReal.ofReal γ},
      ∀ ζ ∈ {ξ : DPath T | rateIT P U T 0 ξ ≤ ENNReal.ofReal γ},
        dM1 ξ ζ < ENNReal.ofReal δ → |PhiT p ξ - PhiT p ζ| < ε := by sorry

end ReflectedRWLDP.SamplePath
