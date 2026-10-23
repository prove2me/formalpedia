-- Prove2me | Theorems.Thm_SLPEPricing_Regret_lemma_2
-- name    : SLPEPricing.Regret.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:33:16.254239+00:00
-- url     : https://prove2.me/theorems/af0d7295-dae4-43ff-b823-3d939e3262ae
-- title:
--   Lemma 2, p. 11 — d″(p*) = 0 with Lipschitz r″ and d′ gives Assumption 1's inequality with κ = Ψ + Ψ̄ + 2K₁
-- statement:
--   Let $d:\mathbb R\to\mathbb R$ be three times continuously differentiable and let $p^*\in(0,1)$ maximise the revenue $r(p)=p\,d(p)$ over $[0,1]$. Assume that
--   1. $r''$ is $\Psi$-Lipschitz and $d'$ is $\bar\Psi$-Lipschitz on $[0,1]$, with $\Psi,\bar\Psi>0$;
--   2. $d''(p^*)=0$;
--   3. $K_1$ bounds $|d^{(k)}(p)|$ for $k=0,1,2,3$ and $p\in[0,1]$.
--
--   Then, with $\kappa=\Psi+\bar\Psi+2K_1$, for every $p\in[0,1]$
--   $$p^*\big(d'(p)-d'(p^*)\big)\le\kappa\,(p-p^*)^2 .$$
--
--   The lemma identifies a concrete class of demand curves, those locally linear at the optimal price, for which the gradient comparison of Lemma 1 holds; it is the paper's justification that Assumption 1 is not restrictive.
--
--   **Formalization Note** Lipschitz continuity (Definition 1, p. 10) is taken on the price range $[0,1]$. $K_1$ is an upper bound on the derivatives rather than their maximum. The conclusion is the inequality the page states after "That is"; $p^*<1$ is added as in Lemma 1.
-- source:
--   Perakis & Singhvi, Dynamic Pricing with Unknown Non-Parametric Demand and Limited Price Changes, SSRN 3336949 (PDF of 2020-07-03), p. 11, Lemma 2 (Definition 1, p. 10; proof App. B, pp. 38–39)

import Mathlib
import Definitions.Def_SLPEPricing_Regret_Model

namespace SLPEPricing.Regret

/-- Lemma 2 (p. 11). `d` is three times continuously differentiable; `r''` is `Ψ`-Lipschitz and
`d'` is `Ψ̄`-Lipschitz on `[0, 1]` (`Ψ, Ψ̄ > 0`, Definition 1); `d''(p*) = 0`; `K₁` bounds
`|d^{(k)}|`, `k ≤ 3`, on `[0, 1]`; `pstar ∈ (0, 1)` maximises `r` on `[0, 1]`. Then
`p*(d'(p) - d'(p*)) ≤ κ(p - p*)²` on `[0, 1]` with `κ = Ψ + Ψ̄ + 2K₁`. -/
theorem lemma_2 (d : ℝ → ℝ) (pstar Ψ Ψbar K₁ : ℝ) (hd : ContDiff ℝ 3 d)
    (hΨ : 0 < Ψ) (hΨbar : 0 < Ψbar)
    (hr2 : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |iteratedDeriv 2 (r d) x - iteratedDeriv 2 (r d) y| ≤ Ψ * |x - y|)
    (hd1 : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |deriv d x - deriv d y| ≤ Ψbar * |x - y|)
    (hpos : 0 < pstar) (hlt : pstar < 1)
    (hmax : ∀ p ∈ Set.Icc (0 : ℝ) 1, r d p ≤ r d pstar)
    (hd2 : iteratedDeriv 2 d pstar = 0)
    (hK₁ : ∀ k ≤ 3, ∀ p ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv k d p| ≤ K₁) :
    ∀ p ∈ Set.Icc (0 : ℝ) 1,
      pstar * (deriv d p - deriv d pstar) ≤ (Ψ + Ψbar + 2 * K₁) * (p - pstar) ^ 2 := by sorry

end SLPEPricing.Regret
