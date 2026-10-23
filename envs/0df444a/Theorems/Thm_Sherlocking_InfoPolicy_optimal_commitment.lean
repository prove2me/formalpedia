-- Prove2me | Theorems.Thm_Sherlocking_InfoPolicy_optimal_commitment
-- name    : Sherlocking.InfoPolicy.optimal_commitment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:26:17.438027+00:00
-- url     : https://prove2.me/theorems/903fa856-b436-4230-915d-7683d5ce5659
-- title:
--   §4, pp. 12–13 (PDF 14–15) — the full-commitment policy solves the platform's commitment problem at fee r, with value Π^C_P(r)
-- statement:
--   Let $\delta<1$ and $K$ satisfy Assumption 1, $1-\delta<K<\delta$, and let $0\le r<1$. For a commitment policy $a:\mathbb R\to[0,1]$ (the probability that the platform enters against type $\theta$), the platform's §4 objective is
--   $$W_r(a)=\int_{\Theta_E(a)}\Big[(1-a(\theta))r\theta + a(\theta)\big((1-\delta)r\theta+\delta\theta-K\big)\Big]d\theta,$$
--   where $\Theta_E(a)=\{\theta\in[0,1] : [(1-\delta)+\delta(1-a(\theta))](1-r)\theta\ge K\}$ is the set of types that enter by (E). Let $a^C_r$ be the full-commitment policy, $a^C_r(\theta)=\alpha(\theta;r)=\frac1\delta\big(1-\frac{K}{(1-r)\theta}\big)$ for $\theta\in[\theta_P(r),1]$ and $a^C_r(\theta)=0$ otherwise. Then:
--
--   1. $W_r(a^C_r)=\Pi^C_P(r)$;
--   2. for every measurable policy $a$ with values in $[0,1]$, $W_r(a)\le\Pi^C_P(r)$;
--   3. if moreover $r<1-K$, then $a^C_r$ is measurable and takes values in $[0,1]$.
--
--   Hence
--   $$\Pi^C_P(r)=\max_{a}W_r(a),$$
--   the maximum taken over measurable $[0,1]$-valued policies and attained at $a^C_r$. This is the reduction of the platform's commitment problem to $\mathcal P_C$, and it identifies the "full commitment outcome" used in §5.
--
--   **Formalization Note** $\delta<1$ is added. For $r\in[1-K,1)$ both cutoffs equal $1$ and both sides of (1) vanish; clause 3 needs $r<1-K$ because $\alpha(1;r)<0$ otherwise. Measurability of $a$ is required because Lean's Bochner integral of a non-measurable function is $0$.
-- source:
--   Choi, Kim & Mukherjee, “Sherlocking” and Platform Information Policy, CESifo Working Paper No. 10769 / SSRN 4643950 (version of November 13, 2023), pp. 12–13 (PDF 14–15), §4, Eq. (E), the platform's problem, footnote 12, the formula for α(θ; r) and problem P_C

import Mathlib
import Definitions.Def_Sherlocking_InfoPolicy_Model

namespace Sherlocking.InfoPolicy

theorem optimal_commitment (K δ r : ℝ) (hδ1 : δ < 1) (hK1 : 1 - δ < K) (hK2 : K < δ) (hr0 : 0 ≤ r) (hr1 : r < 1) : commitPayoff K δ r (commitProb K δ r) = PiC K δ r ∧ (∀ a : ℝ → ℝ, Measurable a → (∀ θ, a θ ∈ Set.Icc (0:ℝ) 1) → commitPayoff K δ r a ≤ PiC K δ r) ∧ (r < 1 - K → Measurable (commitProb K δ r) ∧ ∀ θ, commitProb K δ r θ ∈ Set.Icc (0:ℝ) 1) := by sorry

end Sherlocking.InfoPolicy
