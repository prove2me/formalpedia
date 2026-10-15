-- Prove2me | Theorems.Thm_RefMNLPricing_MultiVsSingle_corollary_4
-- name    : RefMNLPricing.MultiVsSingle.corollary_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T11:43:16.542987+00:00
-- url     : https://prove2.me/theorems/7f9ec8e0-894d-4733-b063-d1caa1d18a07
-- title:
--   Corollary 4, p. 23 — loss-neutral optimal steady state is unique, p_i⋆⋆ = Π⋆⋆ + 1/(b_i + c_iκ), Π⋆⋆ solves (24)
-- statement:
--   Consider the multi-product model with all products loss-neutral, $c_i:=c_i^+=c_i^-$, under the standing assumptions $b>0$, $c\ge0$, $\alpha\in[0,1]$, $\beta\in[0,1)$, $p_H>0$, $p_H\ge\hat p_H$, and let $\kappa=(1-\beta)/(1-\alpha\beta)$. If $p^{\star\star}$ is an optimal steady state, then
--
--   1. it is the only optimal steady state;
--   2. with $\Pi^{\star\star}:=\Pi(p^{\star\star},p^{\star\star})$,
--   $$
--   p_i^{\star\star}=\Pi^{\star\star}+\frac{1}{b_i+c_i\kappa}\quad\forall i\in N;\qquad(23)
--   $$
--   3. $\Pi^{\star\star}$ solves, and is the only solution of,
--   $$
--   \Pi=\sum_{i\in N}\frac{1}{b_i+c_i\kappa}\exp\Big(a_i-b_i\Pi-\frac{b_i}{b_i+c_i\kappa}\Big).\qquad(24)
--   $$
--
--   In this mission, Corollary 4 shows that an optimal steady state of identical products is uniform, which is the basis of Remark 3, and identifies the candidate $p^{\star\star}$ at which condition (28) of Remark 4 is evaluated.
--
--   **Formalization Note.** An optimal steady state is a vector $x\in\mathcal P^n$ for which the constant path $x$ from reference $x$ is optimal. The result does not assert that one exists.
-- source:
--   Guo, Jiang, Shen, Multi-Product Dynamic Pricing with Reference Effects Under Logit Demand, SSRN 4189049 (version of 2024-05-25), p. 23, Corollary 4, (23)–(24)

import Mathlib
import Definitions.Def_RefMNLPricing_MultiVsSingle_Model

namespace RefMNLPricing.MultiVsSingle

/-- Corollary 4, p. 23 (loss-neutral scenario `N = N_n`, `c_i := c_i⁺ = c_i⁻`): an optimal steady
state `p⋆⋆` is unique, satisfies `p_i⋆⋆ = Π⋆⋆ + 1/(b_i + c_i κ)` (23), and `Π⋆⋆ = Π(p⋆⋆, p⋆⋆)` is
the unique solution of (24), with `κ = (1 − β)/(1 − αβ)`. -/
theorem corollary_4 {n : ℕ} (a b cp cm : Fin n → ℝ) (α β pH : ℝ)
    (hb : ∀ i, 0 < b i) (hcp : ∀ i, 0 ≤ cp i) (hcm : ∀ i, 0 ≤ cm i)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Ico (0 : ℝ) 1) (hpH : 0 < pH)
    (hceil : RefMNLPricing.Gap.CeilingOK a b cp cm pH)
    (hneutral : ∀ i, cp i = cm i)
    (x : Fin n → ℝ) (hx : RefMNLPricing.GainSeeking.IsOptSteadyState a b cp cm α β pH x) :
    (∀ y, RefMNLPricing.GainSeeking.IsOptSteadyState a b cp cm α β pH y → y = x) ∧
    (∀ i, x i = RefMNLPricing.Myopic.revenue a b cp cm x x + 1 / (b i + cp i * RefMNLPricing.SteadyState.kappa α β)) ∧
    RefMNLPricing.Myopic.revenue a b cp cm x x = ∑ i, 1 / (b i + cp i * RefMNLPricing.SteadyState.kappa α β) *
      Real.exp (a i - b i * RefMNLPricing.Myopic.revenue a b cp cm x x - b i / (b i + cp i * RefMNLPricing.SteadyState.kappa α β)) ∧
    (∀ R : ℝ, R = ∑ i, 1 / (b i + cp i * RefMNLPricing.SteadyState.kappa α β) *
        Real.exp (a i - b i * R - b i / (b i + cp i * RefMNLPricing.SteadyState.kappa α β)) →
      R = RefMNLPricing.Myopic.revenue a b cp cm x x) := by sorry

end RefMNLPricing.MultiVsSingle
