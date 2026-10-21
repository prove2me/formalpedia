-- Prove2me | Theorems.Thm_SkillData_GoldRush_eq_C5
-- name    : SkillData.GoldRush.eq_C5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:22:39.478864+00:00
-- url     : https://prove2.me/theorems/34075f8e-7f39-46b2-ac6e-e3604cb9832a
-- title:
--   (C5), proof of Proposition 3, p. 35 (PDF 36) — the seller's profit equals βλC(λ)/(1 − β)
-- statement:
--   Under the standing assumptions (in particular $\beta<1$), at every feasible tuple $(x,\lambda,\alpha)$, finite or "as is", the seller's profit satisfies
--   $$\pi=\lambda\,q=\frac{\beta\,\lambda\,C(c,\lambda)}{1-\beta}.$$
--
--   Together with the monotonicity of $C$, the identity reduces the seller's problem (3) to maximizing the mass $\lambda$ of skilled investors.
-- source:
--   Huang, Xiong & Yang, Skill Acquisition and Data Sales, working paper (July 2019 version), p. 35 (PDF 36), proof of Proposition 3, equation (C5)

import Mathlib
import Definitions.Def_SkillData_GoldRush_Model

namespace SkillData.GoldRush

theorem eq_C5 (P : Params) (hP : P.Standing) (C : ℝ → ℝ → ℝ) (c τη : ℝ)
    (X : Clarity) (lam α : ℝ) (hF : Feasible P C c τη X lam α) :
    profit P τη X lam α = P.β * lam * C c lam / (1 - P.β) := by sorry

end SkillData.GoldRush
