-- Prove2me | Theorems.Thm_StabilityDichotomies_Solvability_shared_mask_aggregate_antitone_transport_bound
-- name    : StabilityDichotomies.Solvability.shared_mask_aggregate_antitone_transport_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:36:53.245208+00:00
-- url     : https://prove2.me/theorems/ad8012a7-2d98-4eb3-946e-6a632d25a6a7
-- title:
--   Summed Wasserstein bound for an antitone shared-mask output
-- statement:
--   For 0 < ε ≤ 1, suppose an antitone Boolean mask-output map has at most B false coordinates, and the original and coordinate-deleted output laws are the exact uniform Bernoulli mixtures. The sum of their Wasserstein distances is at most B/ε. Complementing every output gives a monotone map without changing Hamming distances.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535, proof of Theorem 4.3, pp. 16–17, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Definitions.Def_StabilityDichotomies_Approximability_Thinning
noncomputable section
open scoped Classical BigOperators Interval
open MeasureTheory StabilityDichotomies.Solvability

theorem StabilityDichotomies.Solvability.shared_mask_aggregate_antitone_transport_bound (m : ℕ) {V : Type} [Fintype V]
    (out : (Fin m → Bool) → V → Bool) (hanti : Antitone out) (B ε : ℝ)
    (hbound : ∀ mask, (∑ v : V, if !out mask v then (1 : ℝ) else 0) ≤ B)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (μ : PMF (V → Bool)) (ν : Fin m → PMF (V → Bool))
    (hμ : ∀ x, (μ x).toReal = ε⁻¹ * ∫ p in (1-ε)..1,
      ∑ mask : Fin m → Bool, retentionWeight p mask * (if out mask = x then 1 else 0))
    (hν : ∀ i x, (ν i x).toReal = ε⁻¹ * ∫ p in (1-ε)..1,
      ∑ mask : Fin m → Bool, retentionWeight p mask *
        (if out (Function.update mask i false) = x then 1 else 0)) :
    (∑ i, wasserstein μ (ν i)) ≤ B * ε⁻¹ := by sorry
