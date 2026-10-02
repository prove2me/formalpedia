-- Prove2me | Theorems.Thm_TeschlODE_Horseshoe_tent_topEquiv_shift
-- name    : TeschlODE.Horseshoe.tent_topEquiv_shift
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T06:18:09.707292+00:00
-- url     : https://prove2.me/theorems/205e4a13-2b17-4d3c-92ad-68ab4a7d891f
-- title:
--   Theorem 11.5 — for $\mu > 2$, $(\Lambda, T_\mu)$ and $(\Sigma_2, \sigma)$ are topologically equivalent via the itinerary map
-- statement:
--   Let $\mu > 2$, $\Lambda = \Lambda(T_\mu)$, and let $\varphi : \Lambda \to \Sigma_2 = \{0,1\}^{\mathbb{N}_0}$ be the itinerary map (11.23). Then $\varphi$ is a homeomorphism conjugating the tent map to the one-sided shift:
--   $$\sigma \circ \varphi = \varphi \circ T_\mu \quad \text{on } \Lambda.$$
--   Spelled out: $T_\mu$ maps $\Lambda$ into itself; $\varphi$ is a bijection of $\Lambda$ onto $\Sigma_2$; the diagram commutes; $\varphi$ is continuous from $\Lambda$ (distance $|x-y|$) to $\Sigma_2$ (metric (11.24)); and $\varphi^{-1}$ is continuous. Each coordinate of the horseshoe's itinerary map (13.9) is such a one-sided itinerary: the $y$-part for $T_\mu$, the $x$-part for $T_{1/\lambda}$.
--
--   **Formalization Note.** "Topologically equivalent (11.10) via the homeomorphism $\varphi$" is spelled out as the five clauses above. Continuity of $\varphi$ and of $\varphi^{-1}$ is stated in $\varepsilon$–$\delta$ form with the book's metric.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 301, Theorem 11.5

import Mathlib
import Definitions.Def_TeschlODE_Shared_tentMap
import Definitions.Def_TeschlODE_Shared_tentRepellor
import Definitions.Def_TeschlODE_Shared_itinerary
import Definitions.Def_TeschlODE_Shared_shift
import Definitions.Def_TeschlODE_Shared_symDist

namespace TeschlODE.Horseshoe

/-- Teschl, Theorem 11.5, p. 301: for `µ > 2` the dynamical systems `(Λ, T_µ)` and `(Σ₂, σ)` are
topologically equivalent (11.10) via the itinerary map `ϕ` (11.23). Spelled out: `T_µ` maps `Λ`
into itself; `ϕ` is a bijection from `Λ` onto `Σ₂ = {0, 1}^{ℕ₀}`; the diagram commutes,
`σ ∘ ϕ = ϕ ∘ T_µ` on `Λ`; `ϕ` is continuous on `Λ` into `Σ₂` with the metric (11.24); and its
inverse is continuous: for every `x ∈ Λ` and `ε > 0` there is `δ > 0` with `|y − x| < ε`
whenever `y ∈ Λ` and `d(ϕ(y), ϕ(x)) < δ`. -/
theorem tent_topEquiv_shift (μ : ℝ) (hμ : 2 < μ) :
    Set.MapsTo (TeschlODE.Shared.tentMap μ) (TeschlODE.Shared.tentRepellor μ) (TeschlODE.Shared.tentRepellor μ) ∧
      Set.BijOn (TeschlODE.Shared.itinerary μ) (TeschlODE.Shared.tentRepellor μ) Set.univ ∧
      (∀ x ∈ TeschlODE.Shared.tentRepellor μ, TeschlODE.Shared.shift (TeschlODE.Shared.itinerary μ x) = TeschlODE.Shared.itinerary μ (TeschlODE.Shared.tentMap μ x)) ∧
      (∀ x ∈ TeschlODE.Shared.tentRepellor μ, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ y ∈ TeschlODE.Shared.tentRepellor μ, |y - x| < δ →
          TeschlODE.Shared.symDist 2 (TeschlODE.Shared.itinerary μ y) (TeschlODE.Shared.itinerary μ x) < ε) ∧
      (∀ x ∈ TeschlODE.Shared.tentRepellor μ, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ y ∈ TeschlODE.Shared.tentRepellor μ, TeschlODE.Shared.symDist 2 (TeschlODE.Shared.itinerary μ y) (TeschlODE.Shared.itinerary μ x) < δ →
          |y - x| < ε) := by sorry

end TeschlODE.Horseshoe
