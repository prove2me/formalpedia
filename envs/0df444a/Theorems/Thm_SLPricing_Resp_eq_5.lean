-- Prove2me | Theorems.Thm_SLPricing_Resp_eq_5
-- name    : SLPricing.Resp.eq_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:11:26.477259+00:00
-- url     : https://prove2.me/theorems/ebac3d63-bd28-4c9d-9afb-ec483974aba4
-- title:
--   (5), §6.1, p. 19 — without SL, the first-period buyers under responsive pricing are the types $x\ge\chi(p_1)$
-- statement:
--   Consider responsive pricing in the benchmark without social learning ($\gamma=0$, so the posterior mean $q_u$ is $0$ with certainty). Let $p_1$ be a first-period price with $p_1\ge c$, and write $\bar p=\frac{2-\delta_c(1-c)}{2}$.
--
--   1. If $p_1\le\bar p$, the types
--   $$x\ \ge\ \chi(p_1)=\frac{2p_1-c\delta_c}{2-\delta_c}$$
--   buying in period 1, together with an optimal second-period pricing rule, form an equilibrium; and if $\delta_c<1$, in every equilibrium the set of first-period buyers equals $[\chi(p_1),1]$ up to a null set.
--   2. If $p_1>\bar p$, the configuration in which nobody buys in period 1 is an equilibrium, and in every equilibrium the set of first-period buyers is null (adoption inertia).
--
--   This is the benchmark first-period purchasing rule against which the effect of social learning is measured.
--
--   **Formalization Note** The hypothesis $p_1\ge c$ is added: for $p_1<c$ the remaining consumers all value the product below cost, the firm exits in period 2, and the threshold is $p_1$, not the printed $\chi(p_1)$ (e.g. $c=0.5$, $p_1=0.2$, $\delta_c=1$ gives $\chi=-0.1$). Uniqueness is stated for $\delta_c<1$: at $\delta_c=1$ every type above $p_1$ is indifferent between the two periods, and non-threshold equilibria exist (e.g. $c=0$, $p_1=0.3$: the buyer set $[0.55,0.8)\cup(0.85,1]$ is an equilibrium besides $[0.6,1]$). Equilibria are unique only up to null sets because best responses are weak.
-- source:
--   Papanastasiou–Savva, accepted manuscript MS-14-00028.R2 (2016), §6.1, equation (5), p. 19

import Mathlib
import Definitions.Def_SLPricing_Resp_Model
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SLPricing.Resp

/-- (5), §6.1, p. 19: without social learning (`γ = 0`) and for a first-period price `p₁ ≥ c`.
If `p₁ ≤ (2 − δc(1 − c))/2`, the types `[χ(p₁), 1]`, `χ(p₁) = (2p₁ − cδc)/(2 − δc)`, buying
early (with an optimal second-period rule) form an equilibrium, and for `δc < 1` every
equilibrium buyer set equals `[χ(p₁), 1]` up to a null set. If `p₁ > (2 − δc(1 − c))/2`, nobody
buying early is an equilibrium and every equilibrium buyer set is null. -/
theorem eq_5 (P : Params) (hP : P.Standing) (p₁ : ℝ) (hc : P.c ≤ p₁) :
    (p₁ ≤ (2 - P.δc * (1 - P.c)) / 2 →
      (∃ s, IsRespEq P.noSL p₁ (Icc ((2 * p₁ - P.c * P.δc) / (2 - P.δc)) 1) s) ∧
      (P.δc < 1 → ∀ B s, IsRespEq P.noSL p₁ B s →
        B =ᵐ[volume] Icc ((2 * p₁ - P.c * P.δc) / (2 - P.δc)) 1)) ∧
    ((2 - P.δc * (1 - P.c)) / 2 < p₁ →
      (∃ s, IsRespEq P.noSL p₁ ∅ s) ∧
      ∀ B s, IsRespEq P.noSL p₁ B s → volume B = 0) := by sorry

end SLPricing.Resp
