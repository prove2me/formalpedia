-- Prove2me | Theorems.Thm_StochKolmogorov_Extinct_lemma_5_3
-- name    : StochKolmogorov.Extinct.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:33:17.491694+00:00
-- url     : https://prove2.me/theorems/d59aa158-c8c8-47a1-adfb-2b8e393b1387
-- title:
--   Lemma 5.3 — global growth bound for Uθ
-- statement:
--   For the $U_\theta$ defined with weights from (5.2), and $H$ of (3.5), every $\theta\in[0,\delta_0]$, interior state $x$, and time $t\ge0$ satisfy
--
--   $$\mathbb E_x U_\theta(X(t))\le e^{\theta Ht}U_\theta(x).$$
--
--   This controls the same function away from the neighborhood where Proposition 5.1 gives contraction.
--
--   **Moderation note** The expected $U_\theta$ is integrable. The weights are the normalized selection from (5.2).
-- source:
--   Hening, Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, Lemma 5.3, p. 22

import Mathlib
import Definitions.Def_StochKolmogorov_Extinct_Extinction

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Extinct

open EthierKurtz

theorem lemma_5_3 {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (hX : IsSolutionFamily P C B X)
    (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (mu : Measure (SDEState n)) (hmu : mu ∈ bdryErgodic P X)
    (M : ℝ) (hM : IsRadiusM C c γb M)
    (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀)
    (phat : Fin n → ℝ) (hphat : (∀ i ∈ supp mu, 0 < phat i ∧ phat i < δ₀) ∧
      (∑ i ∈ supp mu, phat i) ≤ δ₀)
    (pcheck : ℝ) (hpcheck : 0 < pcheck ∧ pcheck < δ₀) :
    ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) δ₀ →
      ∀ t : ℝ≥0, ∀ x ∈ openOrthant n,
        Integrable (fun ω => Utheta c mu phat pcheck θ (X x t ω)) P ∧
        ∫ ω, Utheta c mu phat pcheck θ (X x t ω) ∂P ≤
          Real.exp (θ * Hconst C c γb δ₀ * (t : ℝ)) * Utheta c mu phat pcheck θ x := by sorry

end StochKolmogorov.Extinct
