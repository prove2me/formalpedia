-- Prove2me | Theorems.Thm_PPDifferentiation_ShortRun_table_1
-- name    : PPDifferentiation.ShortRun.table_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T12:59:09.137984+00:00
-- url     : https://prove2.me/theorems/aeec605c-bb9e-419c-a3ab-7efa915b1416
-- title:
--   Table 1 — stage-1 implementation payoffs
-- statement:
--   Let $t>0$ and $F\ge0$. The firms choose PP or uniform pricing (U) before positioning. For every optimal uniform-leader price in each asymmetric continuation, the net stage-1 payoff matrix, with A's payoff first, is
--
--   $$
--   \begin{array}{c|cc}
--    & B:PP & B:U\\\hline
--   A:PP &(t/8-F,t/8-F)&(t/4-F,t/2)\\
--   A:U &(t/2,t/4-F)&(3t/4,3t/4)
--   \end{array}.
--   $$
--
--   Every entry evaluates a gross pricing-stage payoff at the corresponding positioning outcome; $F$ is subtracted only from a firm that implements PP. This matrix supplies the comparisons in Proposition 5.
--
--   **Formalization Note** The theorem is conditional on the two leader prices being optimal; Proposition 5 also asserts those optima exist. The asymmetric continuation with B implementing PP is obtained by reflection of the source's A-implements-PP case.
-- source:
--   Li, Wang, Nault, Is Personalized Pricing Profitable When Firms Can Differentiate?, working paper, SSRN abstract 3881900 (version of August 3, 2021), §6, p. 25, Table 1

import Mathlib
import Definitions.Def_PPDifferentiation_ShortRun_Setting

namespace PPDifferentiation.ShortRun

theorem table_1 (t F : ℝ) (ht : 0 < t) (hF : 0 ≤ F) :
    ∀ p₀ p₁ : ℝ, PPDifferentiation.Costless.IsLeaderOpt t (1/2) (-1/2) p₀ →
      PPDifferentiation.Costless.IsLeaderOpt t (1/2) (3/2) p₁ →
      stage1A t F p₀ p₁ .PP .PP = t/8 - F ∧
      stage1B t F p₀ p₁ .PP .PP = t/8 - F ∧
      stage1A t F p₀ p₁ .PP .U = t/4 - F ∧
      stage1B t F p₀ p₁ .PP .U = t/2 ∧
      stage1A t F p₀ p₁ .U .PP = t/2 ∧
      stage1B t F p₀ p₁ .U .PP = t/4 - F ∧
      stage1A t F p₀ p₁ .U .U = 3*t/4 ∧
      stage1B t F p₀ p₁ .U .U = 3*t/4 := by sorry

end PPDifferentiation.ShortRun
