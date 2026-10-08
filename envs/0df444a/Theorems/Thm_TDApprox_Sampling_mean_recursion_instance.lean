-- Prove2me | Theorems.Thm_TDApprox_Sampling_mean_recursion_instance
-- name    : TDApprox.Sampling.mean_recursion_instance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:24:36.317632+00:00
-- url     : https://prove2.me/theorems/7d0a8f7f-8a20-4178-aa47-10ef1093ac5e
-- title:
--   §9, p. 25 — scalar mean recurrence for the constructed example
-- statement:
--   For the zero-cost, one-feature construction with every row of $P$ equal to $p$, write $m_t=\mathbb E[r_t]$. The scalar mean of the sampled parameter satisfies
--
--   $$m_{t+1}=(1+\gamma_t\Delta)m_t,\qquad \Delta=\bigl(\alpha(p(s_1)+2p(s_2))-1\bigr)q(s_1)+2\bigl(\alpha(p(s_1)+2p(s_2))-2\bigr)q(s_2).$$
--
--   This is the coefficient calculation at the center of the divergence example. The result also states integrability of every finite-time iterate.
--
--   **Formalization Note** The paper writes states 1 and 2; the statement uses distinct $s_1,s_2$. The parameter is a vector indexed by `Fin 1`, and $m_t$ is its sole coordinate.
-- source:
--   Tsitsiklis & Van Roy, LIDS-P-2322 (1996), Theorem 3 proof, p. 25, specialized recurrence; https://dspace.mit.edu/entities/publication/ab395d25-a6d3-407a-9589-60eaac58fd05

import Mathlib
import Definitions.Def_TDApprox_Sampling_Model

namespace TDApprox.Sampling

open MeasureTheory ProbabilityTheory

theorem mean_recursion_instance
    {S Ω : Type*} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s₁ s₂ : S) (hne : s₁ ≠ s₂)
    (p : Measure S) [IsProbabilityMeasure p] (hp : ∀ i, 0 < p {i})
    (q : S → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq : HasSum q 1)
    (I J : ℕ → Ω → S) (hsample : IsQSample μ q (rowKernel p) I J)
    (α : ℝ) (γ : ℕ → ℝ) (r₀ : Fin 1 → ℝ) :
    ∀ t,
      Integrable (fun ω => qIter α γ (fun _ _ => 0)
        (sampleFeature s₁ s₂) r₀ I J t ω) μ ∧
      (∫ ω, qIter α γ (fun _ _ => 0)
        (sampleFeature s₁ s₂) r₀ I J (t + 1) ω ∂μ) (0 : Fin 1) =
        (1 + γ t *
          (((α * ((p {s₁}).toReal + 2 * (p {s₂}).toReal) - 1) * q s₁) +
            2 * (α * ((p {s₁}).toReal + 2 * (p {s₂}).toReal) - 2) * q s₂)) *
        (∫ ω, qIter α γ (fun _ _ => 0)
          (sampleFeature s₁ s₂) r₀ I J t ω ∂μ) (0 : Fin 1) := by sorry

end TDApprox.Sampling
