-- Prove2me | Theorems.Thm_RefMNLPricing_MultiVsSingle_remark_3
-- name    : RefMNLPricing.MultiVsSingle.remark_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T11:43:09.715854+00:00
-- url     : https://prove2.me/theorems/ff81366c-837f-40f7-8cbf-394e0130234b
-- title:
--   Remark 3, p. 26 — if both the single-price and the optimal policy have steady states, they coincide
-- statement:
--   Consider $n\ge2$ perfect substitutes: all products share the parameters $a$, $b>0$ and loss-neutral reference sensitivity $c=c^+=c^-\ge0$. Assume $\alpha\in[0,1]$, $\beta\in[0,1)$, $p_H>0$ and $p_H\ge\hat p_H$. If $y\in[0,p_H]$ is a steady state of the single-product-based policy (the constant uniform price $y\mathbf 1$ is optimal for the single-price problem (25) from reference $y\mathbf 1$) and $x$ is an optimal steady state of the multi-product problem, then
--   $$
--   x=y\,\mathbf 1 .
--   $$
--
--   So the steady-state revenue is the same under both policies; the comparison in Theorem 7 is therefore about whether a steady state exists at all.
--
--   **Formalization Note.** The paper's justification sentence ("This can be observed from Corollary 4 …") is not part of the statement. The hypothesis $n\ge2$ is the setting of §4.3.
-- source:
--   Guo, Jiang, Shen, Multi-Product Dynamic Pricing with Reference Effects Under Logit Demand, SSRN 4189049 (version of 2024-05-25), p. 26, Remark 3

import Mathlib
import Definitions.Def_RefMNLPricing_MultiVsSingle_Model

namespace RefMNLPricing.MultiVsSingle

/-- Remark 3, p. 26: for `n ≥ 2` products with identical loss-neutral parameters `a, b, c`
(`c = c⁺ = c⁻`), if the single-product-based policy has a steady state `y` and the optimal policy
has a steady state `x`, then `x = y · 1`. -/
theorem remark_3 {n : ℕ} (a b c α β pH : ℝ)
    (hn : 2 ≤ n) (hb : 0 < b) (hc : 0 ≤ c)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Ico (0 : ℝ) 1) (hpH : 0 < pH)
    (hceil : RefMNLPricing.Gap.CeilingOK (fun _ : Fin n => a) (fun _ => b) (fun _ => c) (fun _ => c) pH)
    (y : ℝ) (x : Fin n → ℝ)
    (hy : IsSingleSteadyState (fun _ : Fin n => a) (fun _ => b) (fun _ => c) (fun _ => c)
      α β pH y)
    (hx : RefMNLPricing.GainSeeking.IsOptSteadyState (fun _ : Fin n => a) (fun _ => b) (fun _ => c) (fun _ => c)
      α β pH x) :
    ∀ i, x i = y := by sorry

end RefMNLPricing.MultiVsSingle
