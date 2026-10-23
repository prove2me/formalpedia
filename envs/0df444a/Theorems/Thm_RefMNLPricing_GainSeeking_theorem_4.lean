-- Prove2me | Theorems.Thm_RefMNLPricing_GainSeeking_theorem_4
-- name    : RefMNLPricing.GainSeeking.theorem_4
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-10-14T08:32:58.387982+00:00
-- url     : https://prove2.me/theorems/286851ea-8bde-4179-8c82-87abe9a5ef17
-- title:
--   Theorem 4, p. 20 — with any gain-seeking product the optimal pricing policy admits no steady state
-- statement:
--   Consider the multi-product pricing model with reference effects: $n$ products with MNL demand built from the utilities
--   $$
--   u_i(p,r) = a_i - b_i p_i + c_i^+(r_i-p_i)_+ - c_i^-(p_i-r_i)_+ ,
--   $$
--   where $b_i > 0$ and $c_i^+, c_i^- \ge 0$; single-period revenue $\Pi(p,r) = \sum_i p_i q_i(p,r)$; reference prices updated by $r^{t+1} = \alpha r^t + (1-\alpha) p^t$ with memory $\alpha \in [0,1]$; prices in $[0,p_H]^n$ with $p_H > 0$ at least the root $\hat p_H$ of equation (9); discount factor $\beta\in[0,1)$; and optimal value $V^\star(r^0)$, the supremum of $\sum_t \beta^t\Pi(p^t,r^t)$ over admissible price sequences.
--
--   **Theorem 4 (Non-existence of steady state with gain-seekingness).** If some product is gain-seeking, i.e. $c_i^+ > c_i^-$ for at least one $i$ ($N_g \neq \emptyset$), then the optimal pricing policy admits no steady state: for every $x \in [0,p_H]^n$,
--   $$
--   V^\star(x) > \frac{\Pi(x,x)}{1-\beta},
--   $$
--   so keeping the price constant at $x$ when the reference price is $x$ is never optimal.
--
--   One gain-seeking product suffices, whatever the reference effects of the other products. Together with the corresponding result for the myopic policy (Theorem 3), it shows that with a gain-seeking product both the myopic and the optimal policies are cyclic in the long run.
--
--   **Formalization Note** The hypotheses are $b>0$, $c^\pm\ge0$, $\alpha\in[0,1]$, $\beta\in[0,1)$, $p_H>0$ and the standing ceiling assumption of §2.4 ($p_H \ge \hat p_H$, written as the existence of a root of (9) below $p_H$). No hypothesis on $\alpha<1$ or $\beta>0$ is added, as the page has none. "No steady state" is stated for every $x$ in the box in the sequence form of the mission's Model ($x$ is an optimal steady state when $V^\star(x) \le \Pi(x,x)/(1-\beta)$, i.e. the constant path attains $V^\star(x)$). Since optimal stationary policies need not be unique, this is the statement for every optimal policy, not for a chosen one. $V^\star$ is the supremum over all admissible price sequences.
-- source:
--   Guo, Jiang, Shen, Multi-Product Dynamic Pricing with Reference Effects Under Logit Demand, SSRN 4189049 (version of 2024-05-25), p. 20, Theorem 4

import Mathlib
import Definitions.Def_RefMNLPricing_GainSeeking_Model

namespace RefMNLPricing.GainSeeking

/-- Theorem 4, p. 20: if some product is gain-seeking (`N_g ≠ ∅`), the optimal pricing policy
admits no steady state: no `x ∈ Pⁿ` makes the constant price path `x` optimal from reference `x`. -/
theorem theorem_4 {n : ℕ} (a b cp cm : Fin n → ℝ) (α β pH : ℝ)
    (hb : ∀ i, 0 < b i) (hcp : ∀ i, 0 ≤ cp i) (hcm : ∀ i, 0 ≤ cm i)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Ico (0 : ℝ) 1) (hpH : 0 < pH)
    (hceil : RefMNLPricing.Gap.CeilingOK a b cp cm pH)
    (hgain : ∃ i, IsGainSeeking cp cm i) :
    ∀ x : Fin n → ℝ, ¬ IsOptSteadyState a b cp cm α β pH x := by sorry

end RefMNLPricing.GainSeeking
