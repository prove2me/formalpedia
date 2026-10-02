-- Prove2me | Theorems.Thm_TeschlODE_IntervalMaps_tent_topEquiv_shift
-- name    : TeschlODE.IntervalMaps.tent_topEquiv_shift
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T19:01:38.132802+00:00
-- url     : https://prove2.me/theorems/632ff132-bec2-41fd-9d35-f37ace7d47b3
-- title:
--   Theorem 11.5 — for µ > 2, (Λ, T_µ) and (Σ₂, σ) are topologically equivalent via the itinerary map
-- statement:
--   Let $\mu > 2$, $\Lambda$ the invariant set of the tent map $T_\mu$ and $\varphi : \Lambda \to \Sigma_2$ the itinerary map (11.23). Then $(\Lambda, T_\mu)$ and $(\Sigma_2, \sigma)$ are topologically equivalent via $\varphi$: $T_\mu$ maps $\Lambda$ into itself, $\varphi$ is a homeomorphism of $\Lambda$ (subspace metric of $\mathbb{R}$) onto $\Sigma_2$ (metric (11.24)), and the diagram (11.10) commutes,
--   $$\sigma \circ \varphi = \varphi \circ T_\mu \quad \text{on } \Lambda .$$
--
--   **Formalization Note.** "Homeomorphism" is spelled out in metric form: $\varphi$ is a bijection from $\Lambda$ onto all of $\Sigma_2$; $\varphi$ is continuous at every $x \in \Lambda$ ($\forall \varepsilon > 0\,\exists \delta > 0$, $|y - x| < \delta \Rightarrow d(\varphi(y), \varphi(x)) < \varepsilon$ for $y \in \Lambda$); and $\varphi^{-1}$ is continuous at every $\varphi(x)$ ($\forall \varepsilon > 0\,\exists \delta > 0$, $d(\varphi(y), \varphi(x)) < \delta \Rightarrow |y - x| < \varepsilon$ for $y \in \Lambda$), which, $\varphi$ being a bijection, is continuity of the inverse.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 301, Theorem 11.5

import Mathlib
import Definitions.Def_TeschlODE_Shared_tentMap
import Definitions.Def_TeschlODE_Shared_tentRepellor
import Definitions.Def_TeschlODE_Shared_itinerary
import Definitions.Def_TeschlODE_Shared_shift
import Definitions.Def_TeschlODE_Shared_symDist

namespace TeschlODE.IntervalMaps

/-- Teschl, Theorem 11.5, p. 301: for `µ > 2` the dynamical systems `(Λ, T_µ)` and `(Σ₂, σ)` are
topologically equivalent (11.10) via the itinerary map `ϕ` (11.23). Spelled out: `T_µ` maps `Λ`
into itself; `ϕ` is a bijection from `Λ` onto `Σ₂`; the diagram commutes, `σ ∘ ϕ = ϕ ∘ T_µ` on
`Λ`; `ϕ` is continuous on `Λ` (subspace metric `|x − y|`) into `Σ₂` with the metric (11.24); and
its inverse is continuous, i.e. for every `x ∈ Λ` and `ε > 0` there is `δ > 0` with
`|x − y| < ε` whenever `y ∈ Λ` and `d(ϕ(y), ϕ(x)) < δ`. -/
theorem tent_topEquiv_shift (μ : ℝ) (hμ : 2 < μ) :
    Set.MapsTo (TeschlODE.Shared.tentMap μ) (TeschlODE.Shared.tentRepellor μ) (TeschlODE.Shared.tentRepellor μ) ∧
      Set.BijOn (TeschlODE.Shared.itinerary μ) (TeschlODE.Shared.tentRepellor μ) Set.univ ∧
      (∀ x ∈ TeschlODE.Shared.tentRepellor μ, TeschlODE.Shared.shift (TeschlODE.Shared.itinerary μ x) = TeschlODE.Shared.itinerary μ (TeschlODE.Shared.tentMap μ x)) ∧
      (∀ x ∈ TeschlODE.Shared.tentRepellor μ, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ y ∈ TeschlODE.Shared.tentRepellor μ, |y - x| < δ → TeschlODE.Shared.symDist 2 (TeschlODE.Shared.itinerary μ y) (TeschlODE.Shared.itinerary μ x) < ε) ∧
      (∀ x ∈ TeschlODE.Shared.tentRepellor μ, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ y ∈ TeschlODE.Shared.tentRepellor μ, TeschlODE.Shared.symDist 2 (TeschlODE.Shared.itinerary μ y) (TeschlODE.Shared.itinerary μ x) < δ → |y - x| < ε) := by sorry

end TeschlODE.IntervalMaps
