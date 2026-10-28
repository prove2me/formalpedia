-- Prove2me | Theorems.Thm_SLPEPricing_Regret_lemma_1
-- name    : SLPEPricing.Regret.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:33:14.375637+00:00
-- url     : https://prove2.me/theorems/8f02d684-0cd3-45c6-9d01-a72c6a7bd7de
-- title:
--   Lemma 1, p. 10 — Assumption 1 gives p*(d′(p) − d′(p*)) ≤ κ(p − p*)² on [0, 1]
-- statement:
--   Let $d:\mathbb R\to\mathbb R$ be a differentiable demand curve and let $p^*\in(0,1)$ maximise the revenue $r(p)=p\,d(p)$ over $[0,1]$. Suppose $d$ satisfies Assumption 1 on $[0,1]$ with a constant $\kappa>0$:
--   $$d(p^*)-\kappa(p-p^*)^2\le -d'(p)\,p^*\qquad\text{for all }p\in[0,1].$$
--   Then, for every $p\in[0,1]$,
--   $$p^*\big(d'(p)-d'(p^*)\big)\le\kappa\,(p-p^*)^2 .$$
--
--   The lemma converts Assumption 1 into a one-sided comparison of the demand gradient at an arbitrary price with the gradient at the optimum, which is how the assumption enters the analysis of SLPE.
--
--   **Formalization Note** The page reads "$\forall p\in[0,1]$, $\exists\kappa>0$", which is trivially true (choose $\kappa$ depending on $p$). The statement is posed with Assumption 1's own $\kappa$, uniform in $p$, which is what the proof in Appendix B shows. $p^*<1$ is added so that $p^*$ is an interior maximiser.
-- source:
--   Perakis & Singhvi, Dynamic Pricing with Unknown Non-Parametric Demand and Limited Price Changes, SSRN 3336949 (PDF of 2020-07-03), p. 10, Lemma 1 (Assumption 1, p. 10; proof App. B, p. 38)

import Mathlib
import Definitions.Def_SLPEPricing_Regret_Model

namespace SLPEPricing.Regret

/-- Lemma 1 (p. 10), with Assumption 1's own `κ` (uniform in `p`). `d` is differentiable,
`pstar ∈ (0, 1)` maximises the revenue `r(p) = p d(p)` on `[0, 1]`, and Assumption 1 holds on
`[0, 1]` with `κ > 0`. Then `p*(d'(p) - d'(p*)) ≤ κ(p - p*)²` for every `p ∈ [0, 1]`. -/
theorem lemma_1 (d : ℝ → ℝ) (pstar κ : ℝ) (hd : Differentiable ℝ d)
    (hpos : 0 < pstar) (hlt : pstar < 1)
    (hmax : ∀ p ∈ Set.Icc (0 : ℝ) 1, r d p ≤ r d pstar)
    (hκ : 0 < κ)
    (hA1 : ∀ p ∈ Set.Icc (0 : ℝ) 1, d pstar - κ * (p - pstar) ^ 2 ≤ -(deriv d p) * pstar) :
    ∀ p ∈ Set.Icc (0 : ℝ) 1, pstar * (deriv d p - deriv d pstar) ≤ κ * (p - pstar) ^ 2 := by sorry

end SLPEPricing.Regret
