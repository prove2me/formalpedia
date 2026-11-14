-- Prove2me | Theorems.Thm_StabilityDichotomies_Solvability_shared_mask_aggregate_transport_bound
-- name    : StabilityDichotomies.Solvability.shared_mask_aggregate_transport_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:27:40.819215+00:00
-- url     : https://prove2.me/theorems/9fe1eecd-4540-4cf2-9046-8af2eee344e8
-- title:
--   Summed Wasserstein bound for a monotone shared-mask output
-- statement:
--   For 0 < ε ≤ 1, suppose out is a monotone map from m Boolean occurrence bits to Boolean assignments with at most B ones in each output. Let μ be its exact uniform Bernoulli mixture and, for each coordinate i, let νᵢ be the corresponding mixture after forcing i absent. The sum over i of the Wasserstein distances W₁(μ,νᵢ) is at most B/ε. This combines the integrated shared-mask coupling with the monotone Hamming influence bound. Relating these generic laws to actual erased CSP instances remains a separate step.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535, proof of Theorem 4.3, p. 17, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Definitions.Def_StabilityDichotomies_Approximability_Thinning
noncomputable section
open scoped Classical BigOperators Interval
open MeasureTheory StabilityDichotomies.Solvability

theorem StabilityDichotomies.Solvability.shared_mask_aggregate_transport_bound (m : ℕ) {V : Type} [Fintype V]
    (out : (Fin m → Bool) → V → Bool) (hmono : Monotone out) (B ε : ℝ)
    (hbound : ∀ mask, (∑ v : V, if out mask v then (1 : ℝ) else 0) ≤ B)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (μ : PMF (V → Bool)) (ν : Fin m → PMF (V → Bool))
    (hμ : ∀ x, (μ x).toReal = ε⁻¹ * ∫ p in (1-ε)..1,
      ∑ mask : Fin m → Bool, retentionWeight p mask * (if out mask = x then 1 else 0))
    (hν : ∀ i x, (ν i x).toReal = ε⁻¹ * ∫ p in (1-ε)..1,
      ∑ mask : Fin m → Bool, retentionWeight p mask *
        (if out (Function.update mask i false) = x then 1 else 0)) :
    (∑ i, wasserstein μ (ν i)) ≤ B * ε⁻¹ := by sorry
