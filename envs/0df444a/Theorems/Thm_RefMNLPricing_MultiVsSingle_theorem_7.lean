-- Prove2me | Theorems.Thm_RefMNLPricing_MultiVsSingle_theorem_7
-- name    : RefMNLPricing.MultiVsSingle.theorem_7
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-10-14T11:43:18.06237+00:00
-- url     : https://prove2.me/theorems/45706e42-10d8-4a64-b8be-1bbb4a9ea3da
-- title:
--   Theorem 7, p. 25 — identical loss-neutral substitutes: optimal policy cyclic if the single-price policy is, and under (26) even if not
-- statement:
--   Consider $n\ge2$ perfect substitutes: all products share intrinsic utility $a$, price sensitivity $b>0$ and loss-neutral reference sensitivity $c=c^+=c^-\ge0$. Assume $\alpha\in[0,1]$, $\beta\in[0,1)$, $p_H>0$ and the standing ceiling assumption $p_H\ge\hat p_H$. Compare the multi-product optimal policy $p^\star$ with the **single-product-based policy** $p^s$, the optimal policy of (25) restricted to a common price $y^t\mathbf 1$ for all products.
--
--   1. If $p^s$ admits no steady state (it is cyclic in the long run), then the optimal policy admits no steady state.
--   2. Let $\Pi^{m\star}$ solve $\Pi=\frac{n}{b+c}\exp\big(a-b\Pi-\frac{b}{b+c}\big)$ (equation (18) for identical products), let $p^{m\star}=\Pi^{m\star}+1/(b+c)$ be the common myopic steady-state price, and set
--   $$
--   \zeta_1=\exp(a+\log n+c\,p^{m\star}),\qquad \zeta_2=\frac{2\alpha b+c(\alpha+1)}{(\alpha b+c)(b+c)},\qquad \kappa=\frac{1-\beta}{1-\alpha\beta}.
--   $$
--   If $\alpha b+c>0$ and
--   $$
--   p_H\big[1-\zeta_1e^{-(b+c)p_H}\big]-\zeta_1\zeta_2e^{-(b+c)p_H}\le\zeta_2,\qquad(26a)
--   $$
--   $$
--   \big[(1-\kappa)^2+\beta(1-\alpha\kappa)^2\big]c^2-(1+\beta\alpha^2)(b+c\kappa)^2\ge\frac{(b+c)^2+\beta(\alpha b+c)^2}{n-1},\qquad(26b)
--   $$
--   then $p^s$ admits a steady state while the optimal policy admits none.
--
--   The theorem makes precise the sense in which the multi-product optimal policy is "more likely to be cyclic" than pricing all substitutes at one price.
--
--   **Formalization Note.** "Cyclic" is read as "admits no steady state". A steady state of $p^s$ is a $y\in[0,p_H]$ whose constant uniform path $y\mathbf 1$ is optimal for (25) from reference $y\mathbf 1$; an optimal steady state is an $x\in[0,p_H]^n$ whose constant path is optimal for (5) from reference $x$; "admits no steady state" quantifies over all such points. The phrase "more likely to be cyclic" has no formal content beyond parts 1–2. The hypothesis $\alpha b+c>0$ is added so that $\zeta_2$ is defined; it excludes only $\alpha=c=0$, where (26b) fails anyway. Part 2 is stated with (26a) and (26b) jointly, as the theorem's "a sufficient condition is given by Eq. (26)".
-- source:
--   Guo, Jiang, Shen, Multi-Product Dynamic Pricing with Reference Effects Under Logit Demand, SSRN 4189049 (version of 2024-05-25), p. 25, Theorem 7, (25), (26a)–(26b)

import Mathlib
import Definitions.Def_RefMNLPricing_MultiVsSingle_Model

namespace RefMNLPricing.MultiVsSingle

/-- Theorem 7, p. 25: `n ≥ 2` products with identical loss-neutral parameters `a, b, c`
(`c = c⁺ = c⁻`), under the standing assumptions.
1. If the single-product-based policy `p^s` of (25) admits no steady state, the optimal policy
   admits no steady state.
2. Let `Π^{m⋆}` solve (18) for the identical parameters and `p^{m⋆} = Π^{m⋆} + 1/(b + c)` (17).
   If `αb + c > 0` (so that `ζ₂` is defined) and (26a) and (26b) hold, then `p^s` admits a steady
   state and the optimal policy admits none. -/
theorem theorem_7 {n : ℕ} (a b c α β pH : ℝ)
    (hn : 2 ≤ n) (hb : 0 < b) (hc : 0 ≤ c)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Ico (0 : ℝ) 1) (hpH : 0 < pH)
    (hceil : RefMNLPricing.Gap.CeilingOK (fun _ : Fin n => a) (fun _ => b) (fun _ => c) (fun _ => c) pH) :
    ((¬ ∃ y, IsSingleSteadyState (fun _ : Fin n => a) (fun _ => b) (fun _ => c) (fun _ => c)
          α β pH y) →
      ∀ x : Fin n → ℝ,
        ¬ RefMNLPricing.GainSeeking.IsOptSteadyState (fun _ => a) (fun _ => b) (fun _ => c) (fun _ => c) α β pH x) ∧
    (∀ Rms : ℝ, Rms = n / (b + c) * Real.exp (a - b * Rms - b / (b + c)) →
      0 < α * b + c →
      pH * (1 - zeta1 n a c (Rms + 1 / (b + c)) * Real.exp (-(b + c) * pH))
          - zeta1 n a c (Rms + 1 / (b + c)) * zeta2 α b c * Real.exp (-(b + c) * pH)
          ≤ zeta2 α b c →
      ((1 - RefMNLPricing.SteadyState.kappa α β) ^ 2 + β * (1 - α * RefMNLPricing.SteadyState.kappa α β) ^ 2) * c ^ 2
          - (1 + β * α ^ 2) * (b + c * RefMNLPricing.SteadyState.kappa α β) ^ 2 ≥
          ((b + c) ^ 2 + β * (α * b + c) ^ 2) / ((n : ℝ) - 1) →
      (∃ y, IsSingleSteadyState (fun _ : Fin n => a) (fun _ => b) (fun _ => c) (fun _ => c)
          α β pH y) ∧
      ∀ x : Fin n → ℝ,
        ¬ RefMNLPricing.GainSeeking.IsOptSteadyState (fun _ => a) (fun _ => b) (fun _ => c) (fun _ => c) α β pH x) := by sorry

end RefMNLPricing.MultiVsSingle
