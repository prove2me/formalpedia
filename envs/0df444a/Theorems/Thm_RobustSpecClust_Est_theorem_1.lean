-- Prove2me | Theorems.Thm_RobustSpecClust_Est_theorem_1
-- name    : RobustSpecClust.Est.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T09:43:33.578178+00:00
-- url     : https://prove2.me/theorems/ebc226a7-f7a9-4a15-8558-c4eff2b80128
-- title:
--   Theorem 1, p. 14 — w.p. ≥ 1 − 2r/n_min, ‖X̂_I − X⁰_I‖₁ ≤ Cn²·max{exp(−Δ²min/64σ²max), log n_min/n_min} and (12) (corrected thresholds)
-- statement:
--   **Estimation error for the Robust-LP solution.** Consider $n$ inliers in $\mathbb R^d$ ($d \ge 1$) with fixed labels $\varphi_i \in [r]$, $r \ge 2$, and $m$ outliers. Inlier $i$ is $y_i = \mu_{\varphi_i} + \xi_i$, where the noises $\xi_1,\dots,\xi_n$ are independent, identically distributed within each cluster, and $\xi_i$ is sub-gaussian with parameter $\sigma_{\varphi_i} > 0$ (Definition 3); the outliers $z_1,\dots,z_m$ are arbitrary random vectors. Let $n_k = |\mathcal C_k|$, $n_{\min} = \min_k n_k$, $\Delta_{\min} = \min_{k\ne l}\|\mu_k-\mu_l\|$ and $\sigma_{\max} = \max_k \sigma_k$.
--
--   Fix $\kappa > 0$ and $\upsilon \in (0,1)$, and set
--   $$\theta = \kappa\Delta_{\min},\quad \tau_{\mathrm{in}} = \exp\Big(-\frac{5\Delta^2_{\min}}{64\theta^2}\Big),\quad \tau_{\mathrm{out}} = \exp\Big(-\frac{\Delta^2_{\min}}{4\theta^2}\Big),\quad \gamma = \upsilon\tau_{\mathrm{in}} + (1-\upsilon)\tau_{\mathrm{out}} \in (\tau_{\mathrm{out}}, \tau_{\mathrm{in}}).$$
--   Let $K_{ij} = \exp(-\|y_i - y_j\|^2/2\theta^2)$ over all $N = n+m$ points, $\hat X_{ij} = \mathbb 1\{K_{ij} > \gamma\}$ the Robust-LP solution, and $X^0$ the true clustering matrix. Then there are constants $C, C', C'' > 0$, depending only on $\kappa$ and $\upsilon$, such that whenever $n_{\min} > r$, $\Delta_{\min} \ge 8\sigma_{\max}\sqrt d$ and $m < n$, with probability at least $1 - 2r/n_{\min}$ both
--   $$\|\hat X_{\mathcal I} - X^0_{\mathcal I}\|_1 \le C n^2\max\Big\{\exp\Big(-\frac{\Delta^2_{\min}}{64\sigma^2_{\max}}\Big), \frac{\log n_{\min}}{n_{\min}}\Big\} \qquad (11)$$
--   and
--   $$\frac{\|\hat X - X^0\|_1}{\|X^0\|_1} \le C' r\exp\Big(-\frac{\Delta^2_{\min}}{64\sigma^2_{\max}}\Big) + C'' r\max\Big\{\frac{\log n_{\min}}{n_{\min}}, \frac{m}{n}\Big\} \qquad (12)$$
--   hold. Here $\|\cdot\|_1$ is the entrywise $\ell_1$ norm and $A_{\mathcal I}$ the inlier block.
--
--   The estimation error of the Robust-LP thresholding decays exponentially in the squared signal-to-noise ratio $\Delta^2_{\min}/\sigma^2_{\max}$, up to a $\log n_{\min}/n_{\min}$ sampling term, with arbitrary outliers.
--
--   **Formalization Note**
--   1. *Corrected thresholds.* The page prints $\tau_{\mathrm{in}} = \exp(-5\Delta^2_{\min}/32\theta^2)$ and $\tau^{(k,l)}_{\mathrm{out}} = \exp(-\Delta^2_{kl}/2\theta^2)$ together with the kernel $\exp(-\|\cdot\|^2/2\theta^2)$. That combination is false: the proof reads $K_{ij} < \tau_{\mathrm{in}}$ as $\|y_i-y_j\|^2 > r^2_{\mathrm{in}}$ although the kernel's $2\theta^2$ makes it $\|y_i-y_j\|^2 > 2r^2_{\mathrm{in}}$; a counterexample with $d = 1$, Gaussian noise, $\kappa = 1$, $\upsilon = 1/2$ has a between-cluster linking probability $\approx e^{-0.0108\,\Delta^2/\sigma^2}$, far above $e^{-\Delta^2/64\sigma^2}$. The thresholds here, $\exp(-5\Delta^2_{\min}/64\theta^2)$ and $\exp(-\Delta^2_{kl}/4\theta^2)$ (so $\tau_{\mathrm{out}} = \exp(-\Delta^2_{\min}/4\theta^2)$), are those for which the computations (E.7)–(E.10) of the proof hold.
--   2. *$\theta = \Theta(\Delta_{\min})$* is read as $\theta = \kappa\Delta_{\min}$ (p. 42), and "$\gamma \in (\tau_{\mathrm{out}},\tau_{\mathrm{in}})$" as $\gamma = \upsilon\tau_{\mathrm{in}} + (1-\upsilon)\tau_{\mathrm{out}}$. The "universal constants" depend on $\kappa$ and $\upsilon$ through $\rho_{\min}$ (pp. 42–43), so they are quantified after $\kappa, \upsilon$ and before every model datum.
--   3. *$m < n$* is added for (12); the proof uses it in (E.20)(ii), and (12) fails for $m \gg n$.
--   4. *Labels are fixed*, $\sigma_k$ is the Definition 3 parameter, and the outliers carry no assumption. $d \ge 1$ and $r \ge 2$ make $\Delta_{\min}$ a minimum over a nonempty set and $\theta > 0$.
--   5. The probability statement bounds the outer measure of the failure event by $2r/n_{\min}$.
-- source:
--   arXiv:1912.07546v3, Theorem 1, p. 14, (11)–(12); thresholds corrected per Appendix E, pp. 39–43; m < n from (E.20), p. 43

import Mathlib
import Definitions.Def_RobustSpecClust_Est_Setting
open MeasureTheory ProbabilityTheory

namespace RobustSpecClust.Est

theorem theorem_1 :
    ∀ κ : ℝ, 0 < κ → ∀ υ : ℝ, 0 < υ → υ < 1 →
    ∃ C C' C'' : ℝ, 0 < C ∧ 0 < C' ∧ 0 < C'' ∧
    ∀ (d r n m : ℕ), 1 ≤ d → ∀ (hr : 2 ≤ r),
    ∀ (φ : Fin n → Fin r) (μ : Fin r → E d) (σ : Fin r → ℝ),
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (ξ : Fin n → Ω → E d) (z : Fin m → Ω → E d),
    IsSGMMNoise P φ σ ξ →
    (r : ℝ) < nmin φ (by omega) →
    8 * σmax σ (by omega) * Real.sqrt d ≤ Δmin μ hr →
    m < n →
    let θ := κ * Δmin μ hr
    let τin := Real.exp (-(5 * Δmin μ hr ^ 2) / (64 * θ ^ 2))
    let τout := Real.exp (-(Δmin μ hr ^ 2) / (4 * θ ^ 2))
    let γ := υ * τin + (1 - υ) * τout
    let Xh : Ω → Matrix (Pt n m) (Pt n m) ℝ := fun ω => robustLPSol (kernel θ (dataPoints μ φ ξ z ω)) γ
    let snr := Real.exp (-(Δmin μ hr ^ 2) / (64 * σmax σ (by omega) ^ 2))
    let lr := Real.log (nmin φ (by omega)) / nmin φ (by omega)
    P {ω | ¬ (l1 (inlierBlock (Xh ω) - inlierBlock (trueClust (m := m) φ)) ≤ C * (n : ℝ) ^ 2 * max snr lr ∧
          l1 (Xh ω - trueClust φ) / l1 (trueClust (m := m) φ) ≤
            C' * r * snr + C'' * r * max lr ((m : ℝ) / n))} ≤
      ENNReal.ofReal (2 * r / nmin φ (by omega)) := by sorry

end RobustSpecClust.Est
