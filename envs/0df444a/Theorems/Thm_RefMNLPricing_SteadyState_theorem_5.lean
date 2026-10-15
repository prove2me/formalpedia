-- Prove2me | Theorems.Thm_RefMNLPricing_SteadyState_theorem_5
-- name    : RefMNLPricing.SteadyState.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T10:14:06.342588+00:00
-- url     : https://prove2.me/theorems/36d48a78-c8c7-4cce-b131-812ffcea1954
-- title:
--   Theorem 5, p. 22 — without gain-seeking products every optimal steady state has p_i⋆⋆ − Π(p⋆⋆, p⋆⋆) ∈ [1/(b_i + c_i⁻κ), 1/(b_i + c_i⁺κ)]
-- statement:
--   Consider the reference-effect MNL pricing model with $n$ products, parameters $a$, $b > 0$, $c^+ \ge 0$, $c^- \ge 0$, memory parameter $\alpha \in [0,1]$, discount factor $\beta \in [0,1)$ and price ceiling $p_H > 0$ satisfying the standing ceiling condition $p_H \ge \hat p_H$ of §2.4. Assume the loss-neutral and loss-averse scenario $N = N_l \cup N_n$, i.e. $c_i^+ \le c_i^-$ for every product $i$.
--
--   Then every optimal steady state $p^{\star\star} \in [0, p_H]^n$ and its single-period revenue $\Pi(p^{\star\star}, p^{\star\star})$ satisfy
--   $$
--   p_i^{\star\star} - \Pi(p^{\star\star}, p^{\star\star}) \in \Bigl[\frac{1}{b_i + c_i^-\kappa},\ \frac{1}{b_i + c_i^+\kappa}\Bigr], \qquad \forall i \in N, \qquad (20)
--   $$
--   where $\kappa := (1-\beta)/(1-\alpha\beta)$.
--
--   Here $\Pi(p^{\star\star}, p^{\star\star})$ is the revenue earned when the price equals the reference price, and an optimal steady state is a price vector $x$ such that keeping the price at $x$ forever, starting from reference price $x$, is optimal. The theorem says the markup of each product over the steady-state revenue lies in an explicit interval; since $\kappa \in (0,1]$, the interval is nonempty and shrinks to a point for loss-neutral products. It underlies Corollaries 3 and 4.
--
--   **Formalization Note** "If there exists an optimal steady state, the price $p^{\star\star}$ … admits the structure (20)" is stated for every optimal steady state, since optimal steady states may be non-unique. An optimal steady state is defined through values: $x \in [0,p_H]^n$ and $V^\star(x) \le \Pi(x,x)/(1-\beta)$, where $V^\star$ is the supremum of discounted revenue over all admissible price sequences. The ceiling condition is the paper's standing assumption of §2.4. Products are indexed by `Fin n`.
-- source:
--   Guo, Jiang, Shen, Multi-Product Dynamic Pricing with Reference Effects Under Logit Demand, SSRN 4189049 (version of 2024-05-25), p. 22, Theorem 5, (20)

import Mathlib
import Definitions.Def_RefMNLPricing_SteadyState_Model

namespace RefMNLPricing.SteadyState

/-- Theorem 5 (Steady State Characterization), p. 22, (20): without gain-seeking products
(`c_i⁺ ≤ c_i⁻` for all `i`), every optimal steady state `p⋆⋆` satisfies
`p_i⋆⋆ − Π(p⋆⋆, p⋆⋆) ∈ [1/(b_i + c_i⁻ κ), 1/(b_i + c_i⁺ κ)]` for all `i`,
where `κ = (1 − β)/(1 − αβ)`. -/
theorem theorem_5 {n : ℕ} (a b cp cm : Fin n → ℝ) (α β pH : ℝ)
    (hb : ∀ i, 0 < b i) (hcp : ∀ i, 0 ≤ cp i) (hcm : ∀ i, 0 ≤ cm i)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Ico (0 : ℝ) 1) (hpH : 0 < pH)
    (hceil : RefMNLPricing.Gap.CeilingOK a b cp cm pH)
    (hNoGain : ∀ i, cp i ≤ cm i)
    (x : Fin n → ℝ) (hx : RefMNLPricing.GainSeeking.IsOptSteadyState a b cp cm α β pH x) :
    ∀ i, x i - RefMNLPricing.Myopic.revenue a b cp cm x x ∈
      Set.Icc (1 / (b i + cm i * kappa α β)) (1 / (b i + cp i * kappa α β)) := by sorry

end RefMNLPricing.SteadyState
