-- Prove2me | Theorems.Thm_StochKolmogorov_Extinct_lemma_3_2
-- name    : StochKolmogorov.Extinct.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:33:03.246005+00:00
-- url     : https://prove2.me/theorems/6c8e4522-2047-47d6-8401-bccb63ce8581
-- title:
--   Lemma 3.2 — moment, occupation and Feller estimates
-- statement:
--   Under Assumption 1.1, there are constants $H_1,H_2>0$ such that for every nonnegative start $x$ and $t>0$,
--
--   $$\mathbb E_x(1+c^\top X(t))^{\delta_0}\le H_1+(1+c^\top x)^{\delta_0}e^{-\delta_0\gamma_b t},$$
--
--   and the time integral of $(1+c^\top X(s))^{\delta_0}(1+\sum_i(|f_i(X(s))|+g_i(X(s))^2))$ has expectation at most $H_2((1+c^\top x)^{\delta_0}+t)$. The transition semigroup maps bounded continuous functions on the orthant to continuous functions there.
--
--   The estimates control moments and coefficient integrals; the last clause is the paper's Feller property.
--
--   **Moderation note** The two estimates include integrability of the terminal moment and of the time-space integrand in (3.8).
-- source:
--   Hening, Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, Lemma 3.2, p. 14

import Mathlib
import Definitions.Def_StochKolmogorov_Extinct_Extinction

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Extinct

open EthierKurtz

theorem lemma_3_2 {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (hX : IsSolutionFamily P C B X)
    (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (M : ℝ) (hM : IsRadiusM C c γb M)
    (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀) :
    (∃ H₁ : ℝ, 0 < H₁ ∧ ∃ H₂ : ℝ, 0 < H₂ ∧
      ∀ x ∈ orthant n, ∀ t : ℝ≥0, 0 < t →
        Integrable (fun ω => (1 + ∑ i, c i * X x t ω i) ^ δ₀) P ∧
        Integrable (fun q : ℝ × Ω =>
          (1 + ∑ i, c i * X x q.1.toNNReal q.2 i) ^ δ₀ *
            (1 + ∑ i, (|C.f i (X x q.1.toNNReal q.2)| +
              C.g i (X x q.1.toNNReal q.2) ^ 2)))
          ((volume.restrict (Set.Icc (0 : ℝ) (t : ℝ))).prod P) ∧
        (∫ ω, (1 + ∑ i, c i * X x t ω i) ^ δ₀ ∂P ≤
          H₁ + (1 + ∑ i, c i * x i) ^ δ₀ * Real.exp (-δ₀ * γb * (t : ℝ))) ∧
        (∫ s in (0 : ℝ)..(t : ℝ), ∫ ω,
          (1 + ∑ i, c i * X x s.toNNReal ω i) ^ δ₀ *
            (1 + ∑ i, (|C.f i (X x s.toNNReal ω)| + C.g i (X x s.toNNReal ω) ^ 2)) ∂P
          ≤ H₂ * ((1 + ∑ i, c i * x i) ^ δ₀ + (t : ℝ)))) ∧
    (∀ t : ℝ≥0, ∀ h : SDEState n → ℝ,
      ContinuousOn h (orthant n) →
      (∃ K : ℝ, ∀ x ∈ orthant n, |h x| ≤ K) →
      ContinuousOn (fun x => ∫ ω, h (X x t ω) ∂P) (orthant n)) := by sorry

end StochKolmogorov.Extinct
