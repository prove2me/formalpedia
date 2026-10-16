-- Prove2me | Theorems.Thm_RobustSpecClust_Est_eq_E7
-- name    : RobustSpecClust.Est.eq_E7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T09:43:33.776092+00:00
-- url     : https://prove2.me/theorems/8d4f8515-3684-41f2-b644-4f7a1315b1ac
-- title:
--   (E.7)–(E.8), p. 40 — P(‖ξ_i − ξ_j‖² > 10Δ²min/64) ≤ exp(−Δ²min/64σ²max) within a cluster
-- statement:
--   In the sub-gaussian mixture model with fixed labels ($r \ge 2$ clusters; independent noises, identically distributed within clusters, $\xi_i$ sub-gaussian with parameter $\sigma_{\varphi_i}$), assume $\Delta_{\min} \ge 8\sigma_{\max}\sqrt d$. Then for any two distinct inliers $i \ne j$ of the same cluster,
--   $$\mathbb P\Big(\|\xi_i - \xi_j\|^2 > \frac{10}{64}\Delta_{\min}^2\Big) \le \exp\Big(-\frac{\Delta^2_{\min}}{64\,\sigma^2_{\max}}\Big).$$
--
--   This is (E.7) with the paper's choice $c'^2 = 64$. Since $y_i - y_j = \xi_i - \xi_j$ within a cluster, it bounds the probability $p_{kk}$ that a diagonal-block kernel entry falls below $\tau_{\mathrm{in}}$ ((E.8)).
--
--   **Formalization Note** The constant $c'$ is fixed to $c'^2 = 64$ as on p. 43. The event is stated in distance form, which does not involve $\theta$; with the corrected threshold $\tau_{\mathrm{in}} = \exp(-5\Delta^2_{\min}/64\theta^2)$ and the kernel $\exp(-\|y_i - y_j\|^2/2\theta^2)$, $\{K_{ij} < \tau_{\mathrm{in}}\}$ is exactly this event, which is (E.8). (As printed, $\tau_{\mathrm{in}} = \exp(-r_{\mathrm{in}}^2/\theta^2)$ and the kernel's $2\theta^2$ disagree by a factor 2; see the goal theorem.)
-- source:
--   arXiv:1912.07546v3, Appendix E, displays (E.7)–(E.8), p. 40; c′² = 64 from p. 43

import Mathlib
import Definitions.Def_RobustSpecClust_Est_Setting
open MeasureTheory ProbabilityTheory

namespace RobustSpecClust.Est

theorem eq_E7 {Ω : Type*} [MeasurableSpace Ω] {d n r : ℕ} (hr : 2 ≤ r) (P : Measure Ω)
    [IsProbabilityMeasure P] (φ : Fin n → Fin r) (μ : Fin r → E d) (σ : Fin r → ℝ)
    (ξ : Fin n → Ω → E d) (hξ : IsSGMMNoise P φ σ ξ)
    (hsep : 8 * σmax σ (by omega) * Real.sqrt d ≤ Δmin μ hr)
    (i j : Fin n) (hij : i ≠ j) (hφ : φ i = φ j) :
    P {ω | 10 * Δmin μ hr ^ 2 / 64 < ‖ξ i ω - ξ j ω‖ ^ 2} ≤
      ENNReal.ofReal (Real.exp (-(Δmin μ hr ^ 2) / (64 * σmax σ (by omega) ^ 2))) := by sorry

end RobustSpecClust.Est
