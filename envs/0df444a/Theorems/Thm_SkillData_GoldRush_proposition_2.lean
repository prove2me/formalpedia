-- Prove2me | Theorems.Thm_SkillData_GoldRush_proposition_2
-- name    : SkillData.GoldRush.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:22:39.52799+00:00
-- url     : https://prove2.me/theorems/8753dd20-944e-4db3-b68a-9b58e2b8798f
-- title:
--   Proposition 2 (1), pp. 16–17 (PDF 17–18) — an overall equilibrium exists
-- statement:
--   Fix the parameters under the standing assumptions, an admissible cost family $C$, a cost parameter $c>0$ and a data accuracy $\tau_\eta>0$. Then an overall equilibrium exists: there are a clarity $x^*\in(0,\infty]$, a mass $\lambda^*\in(0,1)$ and a ratio $\alpha^*>0$ that satisfy (14) and (19), and the seller's profit $\lambda^* q^*$ with $q^*=\beta G$ is at least $\lambda q$ for every other feasible $(x,\lambda,\alpha)$:
--   $$\lambda^*\,\beta\,G(x^*,\alpha^*)\;\ge\;\lambda\,\beta\,G(x,\alpha)\qquad\text{for every feasible }(x,\lambda,\alpha).$$
--
--   The statement also shows that the equilibrium notion used by Propositions 3 and 5 is not vacuous.
--
--   **Formalization Note.** Part (2) of the proposition (demand schedules and price function) belongs to the CARA-normal derivation and is not stated. The page's range $x^*\in[0,+\infty]$ is replaced by $(0,\infty]$, because $x=0$ admits no positive root of (14) and would give zero profit.
-- source:
--   Huang, Xiong & Yang, Skill Acquisition and Data Sales, working paper (July 2019 version), pp. 16–17 (PDF 17–18), Proposition 2 (1)

import Mathlib
import Definitions.Def_SkillData_GoldRush_Model

namespace SkillData.GoldRush

theorem proposition_2 (P : Params) (hP : P.Standing) (C : ℝ → ℝ → ℝ)
    (hC : IsCostFamily C) (c τη : ℝ) (hc : 0 < c) (hτη : 0 < τη) :
    ∃ (X : Clarity) (lam α : ℝ), IsEquilibrium P C c τη X lam α := by sorry

end SkillData.GoldRush
