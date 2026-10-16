-- Prove2me | Theorems.Thm_RobustSpecClust_Est_eq_E18
-- name    : RobustSpecClust.Est.eq_E18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T09:43:34.16076+00:00
-- url     : https://prove2.me/theorems/3b97ab20-856d-4920-b42e-2016f75ab26d
-- title:
--   (E.18), p. 43 (corrected thresholds) — τ_in − τ_out = e^{−5/64κ²} − e^{−1/4κ²} > 0 for θ = κΔmin
-- statement:
--   Let $r \ge 2$, centres $\mu_1,\dots,\mu_r \in \mathbb R^d$ with $\Delta_{\min} > 0$, $\kappa > 0$ and $\theta = \kappa\Delta_{\min}$. Put $\tau_{\mathrm{in}} = \exp(-5\Delta^2_{\min}/64\theta^2)$ and $\tau^{(k,l)}_{\mathrm{out}} = \exp(-\Delta^2_{kl}/4\theta^2)$. Then
--   $$\tau_{\mathrm{out}} := \max_{k\ne l}\tau^{(k,l)}_{\mathrm{out}} = \exp\Big(-\frac{\Delta^2_{\min}}{4\theta^2}\Big), \qquad \tau_{\mathrm{in}} - \tau_{\mathrm{out}} = e^{-5/(64\kappa^2)} - e^{-1/(4\kappa^2)} > 0 .$$
--
--   Hence $\rho_{\min} = \min\{\upsilon, 1-\upsilon\}(\tau_{\mathrm{in}} - \tau_{\mathrm{out}})$, the denominator of Lemma 2, is positive and depends only on $\kappa$ and $\upsilon$.
--
--   **Formalization Note** The thresholds are the corrected ones of the goal theorem. The page's chain, in its printed convention with $c'^2 = 64$, ends in $e^{-10/(c'^2\kappa^2)} - e^{-1/(2\kappa^2)}$; in the corrected convention both exponents halve, and the positivity condition $c'^2 > 20$ is unchanged. The page's two "$\ge$" are equalities, which is what is stated.
-- source:
--   arXiv:1912.07546v3, Appendix E, display (E.18), p. 43 (thresholds corrected per Appendix E, pp. 39–43)

import Mathlib
import Definitions.Def_RobustSpecClust_Est_Setting
open MeasureTheory ProbabilityTheory

namespace RobustSpecClust.Est

theorem eq_E18 {d r : ℕ} (hr : 2 ≤ r) (μ : Fin r → E d) (κ : ℝ) (hκ : 0 < κ)
    (hΔ : 0 < Δmin μ hr) :
    let θ := κ * Δmin μ hr
    let τin := Real.exp (-(5 * Δmin μ hr ^ 2) / (64 * θ ^ 2))
    let τout : Fin r → Fin r → ℝ := fun k l => Real.exp (-(sep μ k l ^ 2) / (4 * θ ^ 2))
    tauOutMax τout hr = Real.exp (-(Δmin μ hr ^ 2) / (4 * θ ^ 2)) ∧
    τin - tauOutMax τout hr = Real.exp (-(5 / (64 * κ ^ 2))) - Real.exp (-(1 / (4 * κ ^ 2))) ∧
    0 < Real.exp (-(5 / (64 * κ ^ 2))) - Real.exp (-(1 / (4 * κ ^ 2))) := by sorry

end RobustSpecClust.Est
