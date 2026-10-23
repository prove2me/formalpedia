-- Prove2me | Theorems.Thm_RetailPrivacy_SingleFirm_theorem_1
-- name    : RetailPrivacy.SingleFirm.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T04:13:35.767925+00:00
-- url     : https://prove2.me/theorems/f9c608a0-b065-4abc-a598-3d4fc9bfc5c8
-- title:
--   Theorem 1, p. 17 — for a single firm the GDPR raises profit and welfare, and raises consumer surplus iff v < 2ℳ√(1−δ)/(𝒵√ℱ)
-- statement:
--   Let $c>0$, $\delta\in(0,1)$ and $v>0$, and put
--   $$\mathcal Z = 2c+\delta,\quad \mathcal M = 4c^2(1-\delta)+c\delta(4-3\delta)+\delta^2,\quad \mathcal F = 4c^2(1-\delta)+4c\delta(1-\delta)+\delta^2,\quad \tau = \frac{2\mathcal M\sqrt{1-\delta}}{\mathcal Z\sqrt{\mathcal F}} .$$
--   The single-firm game has a subgame-perfect equilibrium under the $\mathbb R$ mode (before the GDPR) and under the $\mathbb C$ mode (the GDPR). For every equilibrium of the $\mathbb R$ mode and every equilibrium of the $\mathbb C$ mode:
--
--   1. if $v < \tau$, the consumer surplus is strictly higher under the GDPR;
--   2. if $v > \tau$, the consumer surplus is strictly lower under the GDPR;
--   3. the firm's profit is strictly higher under the GDPR;
--   4. social welfare, the firm's profit plus the consumer surplus, is strictly higher under the GDPR.
--
--   The GDPR thus always benefits the firm and society in the single-firm setting, while its effect on consumers reverses at the valuation $\tau$: below it the direct privacy effect dominates, above it the higher price under the GDPR does.
--
--   **Formalization Note** All four comparisons are between on-path outcomes of subgame-perfect profiles of the game defined in the model file, with prices over all of $\mathbb R$ and every off-path subgame specified. The paper's "always increases" for profit and welfare is stated strictly. The hypothesis $v>0$ is implicit in the paper: at $v\le0$ nothing is sold and every outcome is $0$.
-- source:
--   Xu, Wang & Zhang, Consumer Privacy in Online Retail Supply Chains, author manuscript (Management Science, forthcoming; version of November 2024), p. 17, Theorem 1; proof pp. ec23–ec24

import Mathlib
import Definitions.Def_RetailPrivacy_SingleFirm_Model

namespace RetailPrivacy.SingleFirm

theorem theorem_1 (c δ v : ℝ) (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hv : 0 < v) :
    (∃ P : Profile, IsSPE .R v c δ P) ∧
    (∃ P : Profile, IsSPE .C v c δ P) ∧
    ∀ PR PC : Profile, IsSPE .R v c δ PR → IsSPE .C v c δ PC →
      (v < 2 * Mc c δ * Real.sqrt (1 - δ) / (Zc c δ * Real.sqrt (Fc c δ)) →
        eqCS v δ PR < eqCS v δ PC) ∧
      (2 * Mc c δ * Real.sqrt (1 - δ) / (Zc c δ * Real.sqrt (Fc c δ)) < v →
        eqCS v δ PC < eqCS v δ PR) ∧
      eqProfit v c δ PR < eqProfit v c δ PC ∧
      eqWelfare v c δ PR < eqWelfare v c δ PC := by sorry

end RetailPrivacy.SingleFirm
