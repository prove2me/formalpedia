-- Prove2me | Theorems.Thm_RobustSpecClust_Est_eq_E13
-- name    : RobustSpecClust.Est.eq_E13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T09:43:29.866422+00:00
-- url     : https://prove2.me/theorems/c957693f-74fb-4038-8232-eb747be50aaf
-- title:
--   (E.12)–(E.13), p. 41 — w.p. ≥ 1 − 1/n_min, m_c^(k,k) ≤ 2·max{p_kk, c₃ log n_min/n_min}·n_k²
-- statement:
--   There is a constant $c_3 > 0$ such that the following holds in the sub-gaussian mixture model with fixed labels and $n_{\min} > r$. Let $\theta \in \mathbb R$, $\tau_{\mathrm{in}} \le 1$, let $K$ be the kernel matrix of the data, $k$ a cluster, $i_0 \ne j_0$ two inliers of $\mathcal C_k$, and $p_{kk} = \mathbb P(K_{i_0 j_0} < \tau_{\mathrm{in}})$. Then
--   $$\mathbb P\Big(m_c^{(k,k)} > 2\max\Big\{p_{kk}, \frac{c_3\log n_{\min}}{n_{\min}}\Big\}\,n_k^2\Big) \le \frac{1}{n_{\min}} .$$
--
--   The paper obtains this from (E.11) with $c_3 = 2(c_1 + c_2)$. It is the high-probability bound on the number of corrupted entries of one diagonal block.
--
--   **Formalization Note** $c_3$ is existential and universal (quantified before the model), which is the faithful form of the page's $c_3 = 2(c_1+c_2)$ for the unspecified constants of (E.11). $\tau_{\mathrm{in}} \le 1$ is added so that the diagonal $i = j$ (where $K_{ii} = 1$) is never counted; the paper's $\tau_{\mathrm{in}} = \exp(\cdot)$ satisfies it. $n_{\min} > r$ is the standing assumption of Theorem 1 (it makes every cluster nonempty and $\log n_{\min} > 0$). Outliers are arbitrary.
-- source:
--   arXiv:1912.07546v3, Appendix E, displays (E.12)–(E.13), p. 41

import Mathlib
import Definitions.Def_RobustSpecClust_Est_Setting
open MeasureTheory ProbabilityTheory
open Classical

namespace RobustSpecClust.Est

theorem eq_E13 : ∃ c₃ : ℝ, 0 < c₃ ∧
    ∀ {d n m r : ℕ} (hr : 0 < r) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (φ : Fin n → Fin r) (μ : Fin r → E d) (σ : Fin r → ℝ)
      (ξ : Fin n → Ω → E d) (z : Fin m → Ω → E d),
      IsSGMMNoise P φ σ ξ → (r : ℝ) < nmin φ hr →
      ∀ (θ τin : ℝ), τin ≤ 1 →
      ∀ (k : Fin r) (i₀ j₀ : Fin n), φ i₀ = k → φ j₀ = k → i₀ ≠ j₀ →
      let K : Ω → Matrix (Pt n m) (Pt n m) ℝ := fun ω => kernel θ (dataPoints μ φ ξ z ω)
      let p := (P {ω | K ω (Sum.inl i₀) (Sum.inl j₀) < τin}).toReal
      P {ω | 2 * max p (c₃ * Real.log (nmin φ hr) / nmin φ hr) * (clusterSize φ k : ℝ) ^ 2 <
          (mcDiag (K ω) φ τin k : ℝ)} ≤ ENNReal.ofReal (1 / nmin φ hr) := by sorry

end RobustSpecClust.Est
