-- Prove2me | Theorems.Thm_RefMNLPricing_SteadyState_corollary_4
-- name    : RefMNLPricing.SteadyState.corollary_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T10:14:22.092931+00:00
-- url     : https://prove2.me/theorems/42f8ac51-bedb-448d-9a73-9ad8a4a31000
-- title:
--   Corollary 4, p. 23 — with loss-neutral products an optimal steady state is unique and p_i⋆⋆ = Π⋆⋆ + 1/(b_i + c_iκ)
-- statement:
--   Consider the reference-effect MNL pricing model with $n$ products, parameters $a$, $b > 0$, $c^+ \ge 0$, $c^- \ge 0$, memory parameter $\alpha \in [0,1]$, discount factor $\beta \in [0,1)$ and price ceiling $p_H > 0$ satisfying the standing ceiling condition $p_H \ge \hat p_H$ of §2.4. Assume every product is loss-neutral, $c_i := c_i^+ = c_i^-$, and let $\kappa = (1-\beta)/(1-\alpha\beta)$.
--
--   If $p^{\star\star}$ is an optimal steady state, then
--
--   1. it is the only optimal steady state;
--   2. with $\Pi^{\star\star} := \Pi(p^{\star\star}, p^{\star\star})$,
--   $$
--   p_i^{\star\star} = \Pi^{\star\star} + \frac{1}{b_i + c_i\kappa}, \qquad \forall i \in N; \qquad (23)
--   $$
--   3. $\Pi^{\star\star}$ solves
--   $$
--   \Pi = \sum_{i \in N} \frac{1}{b_i + c_i\kappa} \exp\Bigl(a_i - b_i\Pi - \frac{b_i}{b_i + c_i\kappa}\Bigr), \qquad (24)
--   $$
--   and every solution of (24) equals $\Pi^{\star\star}$.
--
--   Under pure loss-neutrality the interval of Theorem 5 collapses to a point, so an optimal steady state, when it exists, is pinned down by one scalar equation. Its structure mirrors the myopic steady state, with the product-specific constants now depending on $\alpha$ and $\beta$ through $\kappa$.
--
--   **Formalization Note** The common value $c_i$ is written as $c_i^+$ in the Lean statement; the hypothesis $c_i^+ = c_i^-$ for all $i$ makes the choice immaterial. "The unique solution of (24)" is split into "solves (24)" and "every solution equals it". Products are indexed by `Fin n`.
-- source:
--   Guo, Jiang, Shen, Multi-Product Dynamic Pricing with Reference Effects Under Logit Demand, SSRN 4189049 (version of 2024-05-25), p. 23, Corollary 4, (23), (24)

import Mathlib
import Definitions.Def_RefMNLPricing_SteadyState_Model

namespace RefMNLPricing.SteadyState

/-- Corollary 4 (Uniqueness of Steady State with Loss-Neutrality), p. 23: if every product is
loss-neutral (`c_i := c_i⁺ = c_i⁻`) and `p⋆⋆` is an optimal steady state, then it is the only one,
`p_i⋆⋆ = Π⋆⋆ + 1/(b_i + c_i κ)` for all `i` (23), and `Π⋆⋆ = Π(p⋆⋆, p⋆⋆)` is the unique solution of
(24) `Π = ∑_i 1/(b_i + c_i κ) · exp(a_i − b_i Π − b_i/(b_i + c_i κ))`. -/
theorem corollary_4 {n : ℕ} (a b cp cm : Fin n → ℝ) (α β pH : ℝ)
    (hb : ∀ i, 0 < b i) (hcp : ∀ i, 0 ≤ cp i) (hcm : ∀ i, 0 ≤ cm i)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Ico (0 : ℝ) 1) (hpH : 0 < pH)
    (hceil : RefMNLPricing.Gap.CeilingOK a b cp cm pH)
    (hNeutral : ∀ i, cp i = cm i)
    (x : Fin n → ℝ) (hx : RefMNLPricing.GainSeeking.IsOptSteadyState a b cp cm α β pH x) :
    (∀ y : Fin n → ℝ, RefMNLPricing.GainSeeking.IsOptSteadyState a b cp cm α β pH y → y = x) ∧
    (∀ i, x i = RefMNLPricing.Myopic.revenue a b cp cm x x + 1 / (b i + cp i * kappa α β)) ∧
    (RefMNLPricing.Myopic.revenue a b cp cm x x = ∑ i, 1 / (b i + cp i * kappa α β) *
        Real.exp (a i - b i * RefMNLPricing.Myopic.revenue a b cp cm x x - b i / (b i + cp i * kappa α β))) ∧
    (∀ z : ℝ, z = ∑ i, 1 / (b i + cp i * kappa α β) *
        Real.exp (a i - b i * z - b i / (b i + cp i * kappa α β)) →
      z = RefMNLPricing.Myopic.revenue a b cp cm x x) := by sorry

end RefMNLPricing.SteadyState
