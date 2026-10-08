-- Prove2me | Theorems.Thm_SuttonBartoRL_LinearTD_td_fixed_point_error_bound
-- name    : SuttonBartoRL.LinearTD.td_fixed_point_error_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T15:08:42.290574+00:00
-- url     : https://prove2.me/theorems/8d5ae308-7cb7-426f-8914-5d2e3e807091
-- title:
--   The TD fixed point exists and $\overline{\mathrm{VE}}(\mathbf w_{\mathrm{TD}}) \le \frac{1}{1-\gamma}\min_{\mathbf w}\overline{\mathrm{VE}}(\mathbf w)$ (9.14)
-- statement:
--   Let a finite MDP with dynamics $p(s', r \mid s, a)$ and a policy $\pi$ be given, in the continuing case with discount rate $0 \le \gamma < 1$, and let $v_\pi$ be the true value function of $\pi$. Let $\mathbf P$ be the transition matrix of the chain induced by $\pi$, $\mu$ a stationary distribution of it with $\mu(s) > 0$ for every state, and $\mathbf X$ an $|\mathcal S| \times d$ feature matrix with linearly independent columns. Let $\mathbf A$ and $\mathbf b$ be as in (9.11) and $\mathbf w_{\mathrm{TD}} = \mathbf A^{-1}\mathbf b$ the TD fixed point (9.12). Then
--
--   1. $\mathbf A$ is invertible, and $\mathbf b = \mathbf A \mathbf w_{\mathrm{TD}}$;
--   2. the mean square value error (9.1) of the TD fixed point is within a factor $1/(1-\gamma)$ of the smallest possible:
--   $$\overline{\mathrm{VE}}(\mathbf w_{\mathrm{TD}}) \le \frac{1}{1 - \gamma}\, \overline{\mathrm{VE}}(\mathbf w) \quad \text{for every } \mathbf w \in \mathbb R^d, \qquad\text{that is,}\qquad \overline{\mathrm{VE}}(\mathbf w_{\mathrm{TD}}) \le \frac{1}{1-\gamma}\min_{\mathbf w} \overline{\mathrm{VE}}(\mathbf w),$$
--   where $\overline{\mathrm{VE}}(\mathbf w) = \sum_s \mu(s)\,[v_\pi(s) - \mathbf w^\top \mathbf x(s)]^2$.
--
--   The asymptotic error of linear semi-gradient TD(0) is therefore no more than $1/(1-\gamma)$ times the error of the best linear approximation, the one attained in the limit by gradient Monte Carlo.
--
--   **Formalization Note** The book cites (9.14) without proof ("it has also been proven (in the continuing case)", p. 207; Tsitsiklis and Van Roy 1997) and leaves its hypotheses implicit; they are stated here: $0 \le \gamma < 1$, $\mu$ the stationary distribution of the chain induced by $\pi$ with every $\mu(s) > 0$, and linearly independent feature columns. $v_\pi$ is the expected discounted return, not defined from $\mathbf w_{\mathrm{TD}}$ or from a Bellman equation, and $\mathbf b$ uses the expected rewards of the MDP. The minimum over $\mathbf w$ is expressed by quantifying over every $\mathbf w$, which is equivalent and avoids a real infimum. The book's constant $1/(1-\gamma)$ is stated, not the sharper $1/(1-\gamma^2)$ of the known proof.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Eq. (9.1), p. 199; Eqs. (9.11)–(9.12), p. 206; Eq. (9.14), p. 207

import Mathlib
import Definitions.Def_SuttonBartoRL_LinearTD_MDP
import Definitions.Def_SuttonBartoRL_LinearTD_LinearTD

open Matrix

namespace SuttonBartoRL.LinearTD

/-- Sutton & Barto (2018), (9.12) and (9.14), pp. 206–207: in the continuing case with `0 ≤ γ < 1`,
let `µ` be a stationary distribution of the chain induced by `π` with every `µ(s) > 0`, and let the
feature matrix `X` have linearly independent columns. Then the `A` matrix (9.11) is invertible, the
TD fixed point `w_TD = A⁻¹b` satisfies `b = Aw_TD`, and its mean square value error with respect to
the true value function `v_π` is within a factor `1/(1 − γ)` of the smallest possible:
`VE(w_TD) ≤ (1/(1 − γ)) VE(w)` for every `w`, i.e. `VE(w_TD) ≤ (1/(1 − γ)) min_w VE(w)`. -/
theorem td_fixed_point_error_bound {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] {d : ℕ}
    (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (μ : S → ℝ) (X : Matrix S (Fin d) ℝ) (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hμ : IsStationaryDist (M.policyTrans π) μ) (hμpos : ∀ s, 0 < μ s)
    (hX : LinearIndependent ℝ Xᵀ) :
    IsUnit (tdA M π μ X γ).det ∧
      tdB M π μ X = tdA M π μ X γ *ᵥ tdFixedPoint M π μ X γ ∧
      ∀ w : Fin d → ℝ,
        VE μ (M.stateValue γ π) X (tdFixedPoint M π μ X γ) ≤
          1 / (1 - γ) * VE μ (M.stateValue γ π) X w := by sorry

end SuttonBartoRL.LinearTD
