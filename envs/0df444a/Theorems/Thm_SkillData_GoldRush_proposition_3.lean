-- Prove2me | Theorems.Thm_SkillData_GoldRush_proposition_3
-- name    : SkillData.GoldRush.proposition_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:22:44.302462+00:00
-- url     : https://prove2.me/theorems/7e463d76-8d5d-4336-b943-f39de8d3ac50
-- title:
--   Proposition 3, p. 17 (PDF 18) — in equilibrium x∗ < ∞ if λ∗τη > α∗γ, and x∗ = ∞ if λ∗τη ≤ α∗γ
-- statement:
--   Fix the parameters under the standing assumptions, a data accuracy $\tau_\eta>0$ and a cost parameter $c$. Let $(x^*,\lambda^*,\alpha^*)$ be an equilibrium. Then:
--
--   1. if $\lambda^*\tau_\eta>\alpha^*\gamma$, the seller adds noise: $x^*<\infty$;
--   2. if $\lambda^*\tau_\eta\le\alpha^*\gamma$, the seller sells the data "as is": $x^*=\infty$.
--
--   The proposition classifies equilibria by the seller's choice of clarity. When the data are sufficiently accurate, the first case obtains.
-- source:
--   Huang, Xiong & Yang, Skill Acquisition and Data Sales, working paper (July 2019 version), p. 17 (PDF 18), Proposition 3

import Mathlib
import Definitions.Def_SkillData_GoldRush_Model

namespace SkillData.GoldRush

theorem proposition_3 (P : Params) (hP : P.Standing) (C : ℝ → ℝ → ℝ) (c τη : ℝ)
    (hτη : 0 < τη) (X : Clarity) (lam α : ℝ) (hE : IsEquilibrium P C c τη X lam α) :
    (α * P.γ < lam * τη → ∃ x : ℝ, X = .finite x) ∧
      (lam * τη ≤ α * P.γ → X = .asIs) := by sorry

end SkillData.GoldRush
