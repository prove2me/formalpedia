-- Prove2me | Theorems.Thm_VerticalOwnership_CompleteInfo_theorem_1
-- name    : VerticalOwnership.CompleteInfo.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:41:10.184276+00:00
-- url     : https://prove2.me/theorems/b74f28c8-7b39-45b1-ba90-d53e61a1eb6f
-- title:
--   Theorem 1, p. 11 — under complete information (q^CI, K^CI) = (0, μ_i + F⁻¹(z_s)) if β < β̲ and (q*, q*) with q* = μ_i + F⁻¹(z_r(β)) if β ≥ β̲, where β̲ < 1
-- statement:
--   Consider the partial-vertical-ownership capacity model under complete information: both firms know the market state $i \in \{L, H\}$. The supplier answers an advance order $q^{adv}$ with the capacity $K_i^{CI}(q^{adv})$ of (5), and the retailer, with ownership share $\beta \in [0,1]$, chooses between ordering nothing and the order $q^* \in \arg\max_{q^{adv} \ge 0} v_r(q^{adv}, q^{adv} \mid \mu_i)$ by the rule (7).
--
--   **Theorem 1.** Define
--   $$\underline\beta = \min\Big\{\beta \in [0,1] : z_r(\beta)\big(F^{-1}(z_r(\beta)) - F^{-1}(z_s)\big) + \big(z_r + \beta(1-z_r)\big)\int_{\underline\varepsilon}^{F^{-1}(z_s)} F(x)\,dx - \int_{\underline\varepsilon}^{F^{-1}(z_r(\beta))} F(x)\,dx \ge 0\Big\},$$
--   with $z_r(\beta) = 1 - (1-z_r)(1-\beta z_s)$ and $z_r = 1 - w/r$. Then:
--   1. the minimum exists and $\underline\beta < 1$;
--   2. for each $i \in \{L, H\}$ and each $\beta \in [0,1]$, the problem (6) has a maximizer $q^* \ge 0$, and for every such maximizer the equilibrium advance order $q_i^{CI}$ of (7) and the capacity $K_i^{CI} = K_i^{CI}(q_i^{CI})$ of (5) are
--   $$\big(q_i^{CI}, K_i^{CI}\big) = \begin{cases} \big(0,\ \mu_i + F^{-1}(z_s)\big) & \beta < \underline\beta,\\ \big(\mu_i + F^{-1}(z_r(\beta)),\ \mu_i + F^{-1}(z_r(\beta))\big) & \beta \ge \underline\beta; \end{cases}$$
--   3. moreover $q_i^{CI}$ maximizes the retailer's accounting payoff $q^{adv} \mapsto v_r(q^{adv}, K_i^{CI}(q^{adv}) \mid \mu_i)$ over all advance orders $q^{adv} \ge 0$.
--
--   So the retailer finances the entire capacity exactly when her ownership share reaches $\underline\beta$, and some share below full ownership always suffices.
--
--   **Formalization Note** The threshold is stated as the least element of the set in (9), together with $\underline\beta < 1$; both existence of the minimum and the bound are conclusions. "arg max" in (6) is read as any maximizer over $q^{adv} \ge 0$ (an advance order is a quantity). Part 3 is §4's meaning of "optimal advance order"; the maximizer of part 3 is not unique in general (for $\beta < 1$ every order up to $\mu_i + \underline\varepsilon$ ties with $0$), which is why $q_i^{CI}$ is defined by the two-option rule (7) as printed. The standing assumptions, including the disclosed additions $c > 0$, integrability of $\varepsilon$ and strict increase of $F$ on its support, are in `Model.Standing`.
-- source:
--   Avinadav, Shamir, Partial Vertical Ownership, Capacity Investment and Information Exchange in a Supply Chain, author manuscript of 2022-06-06 (Management Science, doi:10.1287/mnsc.2023.4673), p. 11, Theorem 1, (8)–(11); objects (5)–(7), p. 10

import Mathlib
import Definitions.Def_VerticalOwnership_CompleteInfo_Setting
open MeasureTheory ProbabilityTheory

namespace VerticalOwnership.CompleteInfo

theorem theorem_1 (M : Model) (hM : M.Standing) :
    ∃ βlow : ℝ, IsLeast {β : ℝ | β ∈ Set.Icc (0 : ℝ) 1 ∧ 0 ≤ M.G9 β} βlow ∧ βlow < 1 ∧
      ∀ μ ∈ ({M.μL, M.μH} : Set ℝ), ∀ β ∈ Set.Icc (0 : ℝ) 1,
        (∃ qs : ℝ, 0 ≤ qs ∧ IsMaxOn (fun q => M.vr β μ q q) (Set.Ici 0) qs) ∧
        ∀ qs : ℝ, 0 ≤ qs → IsMaxOn (fun q => M.vr β μ q q) (Set.Ici 0) qs →
          (M.qCI β μ qs, M.KCI μ (M.qCI β μ qs)) =
              (if β < βlow then ((0 : ℝ), μ + M.Finv M.zs)
               else (μ + M.Finv (M.zrβ β), μ + M.Finv (M.zrβ β))) ∧
            IsMaxOn (fun q => M.vr β μ q (M.KCI μ q)) (Set.Ici 0) (M.qCI β μ qs) := by sorry

end VerticalOwnership.CompleteInfo
