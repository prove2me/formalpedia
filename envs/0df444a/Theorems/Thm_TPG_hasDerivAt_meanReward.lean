-- Prove2me | Theorems.Thm_TPG_hasDerivAt_meanReward
-- name    : TPG.hasDerivAt_meanReward
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-10-12T04:25:27.84745+00:00
-- url     : https://prove2.me/theorems/c44bc9d6-3d72-457b-8f89-29cc97f8874c
-- title:
--   Derivative of the expected reward along a partially varying randomization sequence
-- statement:
--   Let $m_t(q)=\rho^\top P^0_{q_0}P^1_{q_1}\cdots P^{t-1}_{q_{t-1}}\,r_{q_t}$ be the expected reward at time $t$ under a sequence $q$ of treatment probabilities, with $P^s_\theta=\theta P^s_1+(1-\theta)P^s_0$ and $r_\theta=\theta r_1+(1-\theta)r_0$ (time is $0$-indexed).
--
--   Fix a set $A\subseteq\mathbb N$ of times and a sequence $c$, and for a real number $\theta$ let $q^\theta$ be the sequence equal to $\theta$ at the times in $A$ and to $c_s$ at the other times.
--
--   **Lemma.** The function $\theta\mapsto m_t(q^\theta)$ is differentiable at every $\theta_0\in\mathbb R$, with
--
--   $$\frac{d}{d\theta}\,m_t(q^\theta)\Big|_{\theta=\theta_0}=\sum_{u\le t,\ u\in A}\Bigl(m_t\bigl(q^{\theta_0,\,u\to1}\bigr)-m_t\bigl(q^{\theta_0,\,u\to0}\bigr)\Bigr),$$
--
--   where $q^{\theta_0,\,u\to b}$ is $q^{\theta_0}$ with the entry at time $u$ replaced by $b$.
--
--   Since $m_t$ is affine in each coordinate, its derivative along a diagonal direction is the sum of the one-coordinate differences. With $A=\mathbb N$ this is the policy gradient of the value function; with $A=\{u:u+k\ge t\}$ it is the truncated policy gradient.
-- source:
--   Johari, Peng, Xing, Estimation of Treatment Effects Under Nonstationarity via the Truncated Policy Gradient Estimator, revised manuscript of October 2026 (revision of arXiv:2506.05308v3, https://arxiv.org/abs/2506.05308); numbering follows the revised manuscript. Auxiliary statement, not a numbered result of the paper: it is the product rule for d/dθ ρ^⊤ P_θ^{a→b} r_θ of Appendix A.3, p. 27, as used in Appendices G.1, G.3 and G.4, pp. 42–46.

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Estimators
import Definitions.Def_TPG_Markov
import Definitions.Def_TPG_Bridge

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace TPG
theorem hasDerivAt_meanReward {S : Type} [Fintype S] [DecidableEq S]
    (E : Env S) (t : ℕ) (A : ℕ → Prop) [DecidablePred A] (c : ℕ → ℝ) (θ₀ : ℝ) :
    HasDerivAt (fun θ : ℝ => E.meanReward (fun s => if A s then θ else c s) t)
      (∑ u ∈ Finset.range (t + 1),
        if A u then
          (E.meanReward (Function.update (fun s => if A s then θ₀ else c s) u 1) t
            - E.meanReward (Function.update (fun s => if A s then θ₀ else c s) u 0) t)
        else 0)
      θ₀ := by sorry
end TPG
