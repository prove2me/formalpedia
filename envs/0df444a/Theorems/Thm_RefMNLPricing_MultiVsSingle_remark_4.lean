-- Prove2me | Theorems.Thm_RefMNLPricing_MultiVsSingle_remark_4
-- name    : RefMNLPricing.MultiVsSingle.remark_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T11:43:25.322904+00:00
-- url     : https://prove2.me/theorems/ec384cbd-8fc2-4227-a175-061604183dc8
-- title:
--   Remark 4, (28), p. 27 — a sufficient condition for the optimal policy to have no steady state
-- statement:
--   Consider the multi-product model with all products loss-neutral, $c_i:=c_i^+=c_i^-$ (parameters may differ across products), under the standing assumptions $b>0$, $c\ge0$, $\alpha\in[0,1]$, $\beta\in[0,1)$, $p_H>0$, $p_H\ge\hat p_H$. Let $\kappa=(1-\beta)/(1-\alpha\beta)$, let $\Pi^{\star\star}$ solve (24) and let $p^{\star\star}_i=\Pi^{\star\star}+1/(b_i+c_i\kappa)$ be the candidate of Corollary 4. Set
--   $$
--   \kappa_{i,1}=(b_i+c_i)^2+\beta(\alpha b_i+c_i)^2,\qquad \kappa_{i,2}=2(b_i+c_i\kappa)\big[b_i(1+\alpha^2\beta)+c_i(1+\alpha\beta)\big].
--   $$
--   If
--   $$
--   \exists i\in N:\quad \kappa_{i,1}-\kappa_{i,2}>(2\kappa_{i,1}-\kappa_{i,2})\,q_i(p^{\star\star},p^{\star\star}),\qquad(28)
--   $$
--   then the optimal policy admits no steady state: no $x\in\mathcal P^n$ is an optimal steady state.
--
--   This is the general sufficient condition for cyclic long-run behaviour from which (26b) of Theorem 7 is derived.
--
--   **Formalization Note.** The paper evaluates (28) at "$p^{\star\star}$". Since the conclusion is that no optimal steady state exists, $p^{\star\star}$ is read as the unique candidate (23)–(24) of Corollary 4, built from a solution of (24). Remark 4 sits in the loss-neutral setting of §4.3 and writes $c_i$, so the products are taken loss-neutral.
-- source:
--   Guo, Jiang, Shen, Multi-Product Dynamic Pricing with Reference Effects Under Logit Demand, SSRN 4189049 (version of 2024-05-25), p. 27, Remark 4, (28)

import Mathlib
import Definitions.Def_RefMNLPricing_MultiVsSingle_Model

namespace RefMNLPricing.MultiVsSingle

/-- Remark 4, p. 27 (loss-neutral products, `c_i := c_i⁺ = c_i⁻`, possibly different parameters):
let `Π⋆⋆` solve (24) and let `p⋆⋆_i = Π⋆⋆ + 1/(b_i + c_i κ)` be the steady-state candidate (23) of
Corollary 4. If `κ_{i,1} − κ_{i,2} > (2κ_{i,1} − κ_{i,2}) · q_i(p⋆⋆, p⋆⋆)` for some product `i`
(condition (28)), then the optimal policy has no steady state. -/
theorem remark_4 {n : ℕ} (a b cp cm : Fin n → ℝ) (α β pH : ℝ)
    (hb : ∀ i, 0 < b i) (hcp : ∀ i, 0 ≤ cp i) (hcm : ∀ i, 0 ≤ cm i)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Ico (0 : ℝ) 1) (hpH : 0 < pH)
    (hceil : RefMNLPricing.Gap.CeilingOK a b cp cm pH)
    (hneutral : ∀ i, cp i = cm i)
    (Rss : ℝ)
    (hRss : Rss = ∑ i, 1 / (b i + cp i * RefMNLPricing.SteadyState.kappa α β) *
      Real.exp (a i - b i * Rss - b i / (b i + cp i * RefMNLPricing.SteadyState.kappa α β)))
    (h28 : ∃ i, kappa1 b cp α β i - kappa2 b cp α β i >
      (2 * kappa1 b cp α β i - kappa2 b cp α β i) *
        RefMNLPricing.Myopic.share a b cp cm (fun k => Rss + 1 / (b k + cp k * RefMNLPricing.SteadyState.kappa α β))
          (fun k => Rss + 1 / (b k + cp k * RefMNLPricing.SteadyState.kappa α β)) i) :
    ∀ x, ¬ RefMNLPricing.GainSeeking.IsOptSteadyState a b cp cm α β pH x := by sorry

end RefMNLPricing.MultiVsSingle
