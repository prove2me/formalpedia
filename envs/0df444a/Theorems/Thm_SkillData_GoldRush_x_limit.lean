-- Prove2me | Theorems.Thm_SkillData_GoldRush_x_limit
-- name    : SkillData.GoldRush.x_limit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:22:42.746486+00:00
-- url     : https://prove2.me/theorems/2b9e9811-b5b0-4aa7-8aff-0cca5a7d6b3b
-- title:
--   Proof of Proposition 5, p. 38 (PDF 39) — as τη → ∞, the clarity solving (14) tends to 2αγ/(λ(ZH + ZL))
-- statement:
--   Fix the parameters under the standing assumptions, a mass $\lambda>0$ and a ratio $\alpha>0$. As the data accuracy $\tau_\eta$ tends to infinity ($w=1/\tau_\eta\to0$), every positive clarity $x$ that solves (14) for $(\lambda,\alpha)$ converges to
--   $$x(\alpha,\lambda;0)=\frac{2\alpha\gamma}{\lambda(Z_H+Z_L)}.$$
--   That is, for every $\varepsilon>0$ there is $T$ such that, for all $\tau_\eta\ge T$ and every $x>0$ solving (14), $|x-2\alpha\gamma/(\lambda(Z_H+Z_L))|<\varepsilon$.
--
--   This is the leading term of the clarity in the paper's expansion around $w=0$.
--
--   **Formalization Note.** The paper's "when $w=0$" is read as the limit $\tau_\eta\to\infty$, uniformly over the solutions of (14). At $w=0$ itself the model is undefined.
-- source:
--   Huang, Xiong & Yang, Skill Acquisition and Data Sales, working paper (July 2019 version), p. 38 (PDF 39), proof of Proposition 5, 'When w = 0, we have x(α, λ; 0) = 2αγ/(λ(ZH + ZL)) by equation (14)'

import Mathlib
import Definitions.Def_SkillData_GoldRush_Model

namespace SkillData.GoldRush

theorem x_limit (P : Params) (hP : P.Standing) (lam α : ℝ) (hlam : 0 < lam) (hα : 0 < α) :
    ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ τη : ℝ, T ≤ τη → ∀ x : ℝ, 0 < x → Eq14 P τη x lam α →
      |x - 2 * α * P.γ / (lam * (P.ZH + P.ZL))| < ε := by sorry

end SkillData.GoldRush
