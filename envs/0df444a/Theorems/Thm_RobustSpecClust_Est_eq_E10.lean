-- Prove2me | Theorems.Thm_RobustSpecClust_Est_eq_E10
-- name    : RobustSpecClust.Est.eq_E10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T09:43:32.719753+00:00
-- url     : https://prove2.me/theorems/2ae52814-6818-4d45-a84a-75e9fa095fe2
-- title:
--   (E.9)–(E.10), p. 41 — P(‖y_i − y_j‖² < ρ) ≤ exp(−(Δ²_kl − ρ)²/(16σ²max Δ²_kl)) across clusters
-- statement:
--   In the sub-gaussian mixture model with fixed labels ($r \ge 2$), let $i, j$ be inliers in different clusters $k = \varphi_i \ne l = \varphi_j$, with $y_i = \mu_k + \xi_i$ and $y_j = \mu_l + \xi_j$, and let $0 \le \rho < \Delta_{kl}^2$. Then
--   $$\mathbb P\big(\|y_i - y_j\|^2 < \rho\big) \le \exp\Big(-\frac{(\Delta_{kl}^2 - \rho)^2}{16\,\sigma^2_{\max}\,\Delta^2_{kl}}\Big).$$
--
--   Here $\rho$ plays the role of $r^{kl\,2}_{\mathrm{out}}$. With $\rho = \Delta^2_{kl}/2$ the bound is $\exp(-\Delta^2_{kl}/64\sigma^2_{\max})$ ((E.17)(iv)). It bounds the probability $p_{kl}$ that an off-diagonal kernel entry exceeds its threshold.
--
--   **Formalization Note** The event is in distance form; under the corrected $\tau^{(k,l)}_{\mathrm{out}} = \exp(-\Delta^2_{kl}/4\theta^2)$, $\{K_{ij} > \tau^{(k,l)}_{\mathrm{out}}\} = \{\|y_i - y_j\|^2 < \Delta^2_{kl}/2\}$. The page's step "$= \mathbb P(2(\mu_k-\mu_l)^\top(\xi_i-\xi_j) > \Delta^2_{kl} - r^2)$" uses a symmetry the model does not provide; the bound holds anyway through the lower tail of the sub-gaussian variable, and no symmetry is assumed. The nonnegative squared radius and the strict upper bound ensure $\Delta_{kl}>0$, so the denominator expresses the paper's quantity without a zero-division value.
-- source:
--   arXiv:1912.07546v3, Appendix E, displays (E.9)–(E.10), p. 41

import Mathlib
import Definitions.Def_RobustSpecClust_Est_Setting
open MeasureTheory ProbabilityTheory

namespace RobustSpecClust.Est

theorem eq_E10 {Ω : Type*} [MeasurableSpace Ω] {d n r : ℕ} (hr : 2 ≤ r) (P : Measure Ω)
    [IsProbabilityMeasure P] (φ : Fin n → Fin r) (μ : Fin r → E d) (σ : Fin r → ℝ)
    (ξ : Fin n → Ω → E d) (hξ : IsSGMMNoise P φ σ ξ)
    (i j : Fin n) (hφ : φ i ≠ φ j) (ρ : ℝ) (hρnonneg : 0 ≤ ρ)
    (hρ : ρ < sep μ (φ i) (φ j) ^ 2) :
    P {ω | ‖(μ (φ i) + ξ i ω) - (μ (φ j) + ξ j ω)‖ ^ 2 < ρ} ≤
      ENNReal.ofReal (Real.exp (-((sep μ (φ i) (φ j) ^ 2 - ρ) ^ 2) /
        (16 * σmax σ (by omega) ^ 2 * sep μ (φ i) (φ j) ^ 2))) := by sorry

end RobustSpecClust.Est
