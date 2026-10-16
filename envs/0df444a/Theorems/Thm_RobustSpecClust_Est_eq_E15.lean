-- Prove2me | Theorems.Thm_RobustSpecClust_Est_eq_E15
-- name    : RobustSpecClust.Est.eq_E15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T09:43:47.682117+00:00
-- url     : https://prove2.me/theorems/5daf55f5-6d46-4f58-8867-01dbea541ebc
-- title:
--   (E.15), p. 42 — w.p. ≥ 1 − 1/n²_min, m_c^(k,l) ≤ 2·max{p_kl, c log n_min/n_min}·n_k n_l
-- statement:
--   There is a constant $c > 0$ such that the following holds in the sub-gaussian mixture model with fixed labels and $n_{\min} > r$. Let $\theta \in \mathbb R$ and thresholds $\tau^{(k,l)}_{\mathrm{out}}$ be given, let $K$ be the kernel matrix of the data, $k \ne l$ two clusters, $i_0 \in \mathcal C_k$, $j_0 \in \mathcal C_l$, and $p_{kl} = \mathbb P(K_{i_0 j_0} > \tau^{(k,l)}_{\mathrm{out}})$. Then
--   $$\mathbb P\Big(m_c^{(k,l)} > 2\max\Big\{p_{kl}, \frac{c\log n_{\min}}{n_{\min}}\Big\}\,n_k n_l\Big) \le \frac{1}{n^2_{\min}} .$$
--
--   The paper obtains this from (E.14) with $c = 2(c_4 + c_5)$. It is the high-probability bound on the number of corrupted entries of one off-diagonal block.
--
--   **Formalization Note** $c$ is existential and universal, the faithful form of the page's $2(c_4+c_5)$. $n_{\min} > r$ is the standing assumption of Theorem 1. Outliers are arbitrary.
-- source:
--   arXiv:1912.07546v3, Appendix E, display (E.15), p. 42

import Mathlib
import Definitions.Def_RobustSpecClust_Est_Setting
open MeasureTheory ProbabilityTheory
open Classical

namespace RobustSpecClust.Est

theorem eq_E15 : ∃ c : ℝ, 0 < c ∧
    ∀ {d n m r : ℕ} (hr : 0 < r) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (φ : Fin n → Fin r) (μ : Fin r → E d) (σ : Fin r → ℝ)
      (ξ : Fin n → Ω → E d) (z : Fin m → Ω → E d),
      IsSGMMNoise P φ σ ξ → (r : ℝ) < nmin φ hr →
      ∀ (θ : ℝ) (τout : Fin r → Fin r → ℝ),
      ∀ (k l : Fin r) (i₀ j₀ : Fin n), k ≠ l → φ i₀ = k → φ j₀ = l →
      let K : Ω → Matrix (Pt n m) (Pt n m) ℝ := fun ω => kernel θ (dataPoints μ φ ξ z ω)
      let p := (P {ω | τout k l < K ω (Sum.inl i₀) (Sum.inl j₀)}).toReal
      P {ω | 2 * max p (c * Real.log (nmin φ hr) / nmin φ hr) *
            ((clusterSize φ k : ℝ) * (clusterSize φ l : ℝ)) < (mcOff (K ω) φ τout k l : ℝ)} ≤
        ENNReal.ofReal (1 / nmin φ hr ^ 2) := by sorry

end RobustSpecClust.Est
