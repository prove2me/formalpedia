-- Prove2me | Theorems.Thm_RefMNLPricing_SteadyState_corollary_3
-- name    : RefMNLPricing.SteadyState.corollary_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T10:14:18.288599+00:00
-- url     : https://prove2.me/theorems/0d9e6ce8-614b-43a7-bb4e-48fcad28fb5f
-- title:
--   Corollary 3, p. 22 — optimal steady states satisfy Π(p⋆⋆, p⋆⋆) ∈ [Π^L, Π^U] and p_i⋆⋆ ∈ [Π^L + 1/(b_i + c_i⁻κ), Π^U + 1/(b_i + c_i⁺κ)]
-- statement:
--   Consider the reference-effect MNL pricing model with $n$ products, parameters $a$, $b > 0$, $c^+ \ge 0$, $c^- \ge 0$, memory parameter $\alpha \in [0,1]$, discount factor $\beta \in [0,1)$ and price ceiling $p_H > 0$ satisfying the standing ceiling condition $p_H \ge \hat p_H$ of §2.4. Assume no product is gain-seeking: $c_i^+ \le c_i^-$ for every $i$. Let $\kappa = (1-\beta)/(1-\alpha\beta)$.
--
--   1. Each of the equations
--   $$
--   \Pi = \sum_{i \in N} \frac{1}{b_i + c_i^-\kappa} \exp\Bigl(a_i - b_i\Pi - \frac{b_i}{b_i + c_i^+\kappa}\Bigr) \qquad (22a)
--   $$
--   $$
--   \Pi = \sum_{i \in N} \frac{1}{b_i + c_i^+\kappa} \exp\Bigl(a_i - b_i\Pi - \frac{b_i}{b_i + c_i^-\kappa}\Bigr) \qquad (22b)
--   $$
--   has exactly one real solution; call them $\Pi^L$ and $\Pi^U$.
--   2. For every optimal steady state $p^{\star\star}$,
--   $$
--   \Pi(p^{\star\star}, p^{\star\star}) \in [\Pi^L, \Pi^U], \qquad p_i^{\star\star} \in \Bigl[\Pi^L + \frac{1}{b_i + c_i^-\kappa},\ \Pi^U + \frac{1}{b_i + c_i^+\kappa}\Bigr] \quad \forall i \in N. \qquad (21)
--   $$
--
--   The bounds $\Pi^L$, $\Pi^U$ come from one-dimensional equations, so the corollary turns the implicit interval condition of Theorem 5 into an explicit range for every optimal steady state price; prices outside it can never be optimal steady states.
--
--   **Formalization Note** The corollary is stated in the scenario of Theorem 5 ($c_i^+ \le c_i^-$ for all $i$), which the paper derives it from; the printed corollary does not repeat that hypothesis. Uniqueness in (22a)–(22b) is stated with `∃!`, and the bounds are stated for every solution of each equation, so no solution is chosen. The paper's remark that $\Pi^L$, $\Pi^U$ can be computed by bisection is not formalized. The coefficient pairs of (22a) and (22b) are crossed exactly as printed. Products are indexed by `Fin n`.
-- source:
--   Guo, Jiang, Shen, Multi-Product Dynamic Pricing with Reference Effects Under Logit Demand, SSRN 4189049 (version of 2024-05-25), p. 22, Corollary 3, (21), (22a), (22b)

import Mathlib
import Definitions.Def_RefMNLPricing_SteadyState_Model

namespace RefMNLPricing.SteadyState

/-- Corollary 3, p. 22, in the scenario of Theorem 5 (`c_i⁺ ≤ c_i⁻` for all `i`).
(a) Each of (22a) `Π = ∑_i 1/(b_i + c_i⁻κ) · exp(a_i − b_i Π − b_i/(b_i + c_i⁺κ))` and
(22b) `Π = ∑_i 1/(b_i + c_i⁺κ) · exp(a_i − b_i Π − b_i/(b_i + c_i⁻κ))` has a unique solution.
(b) If `Π^L` solves (22a), `Π^U` solves (22b) and `p⋆⋆` is an optimal steady state, then
`Π(p⋆⋆, p⋆⋆) ∈ [Π^L, Π^U]` and, (21), `p_i⋆⋆ ∈ [Π^L + 1/(b_i + c_i⁻κ), Π^U + 1/(b_i + c_i⁺κ)]`. -/
theorem corollary_3 {n : ℕ} (a b cp cm : Fin n → ℝ) (α β pH : ℝ)
    (hb : ∀ i, 0 < b i) (hcp : ∀ i, 0 ≤ cp i) (hcm : ∀ i, 0 ≤ cm i)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Ico (0 : ℝ) 1) (hpH : 0 < pH)
    (hceil : RefMNLPricing.Gap.CeilingOK a b cp cm pH)
    (hNoGain : ∀ i, cp i ≤ cm i) :
    (∃! z : ℝ, z = ∑ i, 1 / (b i + cm i * kappa α β) *
        Real.exp (a i - b i * z - b i / (b i + cp i * kappa α β))) ∧
    (∃! z : ℝ, z = ∑ i, 1 / (b i + cp i * kappa α β) *
        Real.exp (a i - b i * z - b i / (b i + cm i * kappa α β))) ∧
    ∀ PiL PiU : ℝ,
      PiL = ∑ i, 1 / (b i + cm i * kappa α β) *
        Real.exp (a i - b i * PiL - b i / (b i + cp i * kappa α β)) →
      PiU = ∑ i, 1 / (b i + cp i * kappa α β) *
        Real.exp (a i - b i * PiU - b i / (b i + cm i * kappa α β)) →
      ∀ x : Fin n → ℝ, RefMNLPricing.GainSeeking.IsOptSteadyState a b cp cm α β pH x →
        RefMNLPricing.Myopic.revenue a b cp cm x x ∈ Set.Icc PiL PiU ∧
        ∀ i, x i ∈ Set.Icc (PiL + 1 / (b i + cm i * kappa α β))
          (PiU + 1 / (b i + cp i * kappa α β)) := by sorry

end RefMNLPricing.SteadyState
