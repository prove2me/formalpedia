-- Prove2me | Theorems.Thm_SkillData_GoldRush_alpha_limit
-- name    : SkillData.GoldRush.alpha_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:22:54.051406+00:00
-- url     : https://prove2.me/theorems/6bd437b4-5a35-4916-b3db-f9c82403780b
-- title:
--   Proof of Proposition 5, p. 39 (PDF 40) — as τη → ∞, the equilibrium α∗ tends to √(τθ/τu)
-- statement:
--   Fix the parameters under the standing assumptions, an admissible cost family $C$ and a cost parameter $c>0$. As the data accuracy $\tau_\eta$ tends to infinity, the ratio $\alpha^*$ of every equilibrium converges to
--   $$\alpha(\lambda;0)=\sqrt{\tau_\theta/\tau_u}.$$
--   That is, for every $\varepsilon>0$ there is $T$ such that, for all $\tau_\eta\ge T$ and every equilibrium $(x^*,\lambda^*,\alpha^*)$ at $(c,\tau_\eta)$, $|\alpha^*-\sqrt{\tau_\theta/\tau_u}|<\varepsilon$.
--
--   The paper obtains this value as the root of the seller's first-order condition $\Omega(\alpha,\lambda;0)=2\gamma(\tau_\theta-\tau_u\alpha^2)/(\lambda(Z_H+Z_L))=0$ at $w=0$. The limit is the leading term of price informativeness for accurate data.
--
--   **Formalization Note.** The paper's statement about the $w=0$ first-order condition is formalized as the convergence of the exact finite-$\tau_\eta$ equilibrium ratio. The function $\Omega$ is not defined.
-- source:
--   Huang, Xiong & Yang, Skill Acquisition and Data Sales, working paper (July 2019 version), p. 39 (PDF 40), proof of Proposition 5, 'When w = 0, Ω(α, λ; 0) = 2γ(τθ − τuα²)/(λ(ZH + ZL)), and Ω(α, λ; 0) = 0 yields α(λ; 0) = √(τθ/τu)'

import Mathlib
import Definitions.Def_SkillData_GoldRush_Model

namespace SkillData.GoldRush

theorem alpha_limit (P : Params) (hP : P.Standing) (C : ℝ → ℝ → ℝ) (hC : IsCostFamily C)
    (c : ℝ) (hc : 0 < c) :
    ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ τη : ℝ, T ≤ τη →
      ∀ (X : Clarity) (lam α : ℝ), IsEquilibrium P C c τη X lam α →
        |α - Real.sqrt (P.τθ / P.τu)| < ε := by sorry

end SkillData.GoldRush
