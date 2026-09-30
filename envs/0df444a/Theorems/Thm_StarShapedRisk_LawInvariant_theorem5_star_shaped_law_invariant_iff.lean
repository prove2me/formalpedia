-- Prove2me | Theorems.Thm_StarShapedRisk_LawInvariant_theorem5_star_shaped_law_invariant_iff
-- name    : StarShapedRisk.LawInvariant.theorem5_star_shaped_law_invariant_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T23:11:57.103+00:00
-- url     : https://prove2.me/theorems/99ae38ab-bba1-4e64-ae96-dc0de7bde804
-- title:
--   Theorem 5 (i)⇔(ii) — star-shaped law-invariant risk measures are robustified VaR
-- statement:
--   Let $P$ be an atomless probability measure on $(\Omega,\mathcal F)$ and let $\mathcal X$ be the space of bounded measurable losses with the pointwise order. For a function $\rho:\mathcal X\to\mathbb R$ the following are equivalent:
--
--   1. $\rho$ is a star-shaped and law-invariant risk measure;
--   2. there is a star-shaped set $\mathcal G$ of increasing functions $g:(0,1)\to\mathbb R$ with $g(0+)\le 0$ such that
--   $$\rho(X)=\inf_{g\in\mathcal G}\ \sup_{\alpha\in(0,1)}\ \{\mathrm{VaR}_\alpha(X)-g(\alpha)\}\qquad\text{for all }X\in\mathcal X. \tag{25}$$
--
--   Here "increasing" is weak monotonicity, $g(0+)=\lim_{\alpha\downarrow 0}g(\alpha)=\inf_{\alpha\in(0,1)}g(\alpha)$ may be $-\infty$, and a set $\mathcal G$ of functions is star-shaped if $\lambda g\in\mathcal G$ for all $g\in\mathcal G$ and $\lambda\in[0,1]$.
--
--   The theorem shows that star-shaped law-invariant risk measures are exactly the robustifications of Value-at-Risk obtained by penalising each level $\alpha$ with a benchmark $g(\alpha)$ and taking the most favourable benchmark in $\mathcal G$. It parallels Theorem 4, where ES replaces VaR and SSD-consistency replaces law invariance. The paper's "Moreover" clause (closure under the operations of Theorem 1) is not part of this statement.
--
--   **Formalization Note** The functions $g$ have domain exactly the open interval $(0,1)$. The inner supremum can be $+\infty$ for some $g$, so both sides of (25) are compared in the extended reals $[-\infty,+\infty]$; the left side is the real number $\rho(X)$, which forces the infimum to be finite (in particular $\mathcal G\neq\emptyset$). The condition $g(0+)\le 0$ is written as $\inf_{\alpha\in(0,1)}g(\alpha)\le 0$ in the extended reals. In (ii), $\rho$ is an arbitrary real function; none of the risk-measure axioms is assumed there.
-- source:
--   Castagnoli, Cattelan, Maccheroni, Tebaldi, Wang, Star-Shaped Risk Measures, Operations Research 70(5) (2022), pp. 2646–2647, Theorem 5 (i)⇔(ii), Eq. (25); standing assumption of Sec. 7, p. 2646

import Mathlib
import Definitions.Def_StarShapedRisk_LawInvariant_Model
import Definitions.Def_StarShapedRisk_LawInvariant_VaR

namespace StarShapedRisk.LawInvariant

open MeasureTheory

/-- Castagnoli et al. (2022), Theorem 5 (i)⇔(ii) (pp. 2646–2647). On an atomless probability
space, a function `ρ` on bounded measurable positions is a star-shaped, law-invariant risk
measure if and only if there is a star-shaped set `G` of increasing functions
`g : (0,1) → ℝ` with `g(0+) ≤ 0` such that
`ρ X = inf_{g ∈ G} sup_{α ∈ (0,1)} (VaR_α(X) - g α)` for every `X`
(computed in the extended reals). -/
theorem theorem5_star_shaped_law_invariant_iff {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hP : IsAtomless P)
    (ρ : Positions Ω → ℝ) :
    (IsRiskMeasure ρ ∧ IsStarShaped ρ ∧ IsLawInvariant P ρ) ↔
      ∃ G : Set (Set.Ioo (0 : ℝ) 1 → ℝ),
        StarConvex ℝ 0 G ∧
        (∀ g ∈ G, Monotone g ∧ ⨅ α : Set.Ioo (0 : ℝ) 1, (g α : EReal) ≤ 0) ∧
        ∀ X : Positions Ω,
          (ρ X : EReal) =
            ⨅ g ∈ G, ⨆ α : Set.Ioo (0 : ℝ) 1, ((VaR P α X.1 - g α : ℝ) : EReal) := by sorry

end StarShapedRisk.LawInvariant
