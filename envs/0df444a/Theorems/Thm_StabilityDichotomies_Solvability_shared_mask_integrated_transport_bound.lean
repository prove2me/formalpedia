-- Prove2me | Theorems.Thm_StabilityDichotomies_Solvability_shared_mask_integrated_transport_bound
-- name    : StabilityDichotomies.Solvability.shared_mask_integrated_transport_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:14:43.984053+00:00
-- url     : https://prove2.me/theorems/f5e64ae3-8822-445a-952a-e5668bef9a2d
-- title:
--   Integrated shared-mask Wasserstein bound for forced deletion
-- statement:
--   Let out map finite occurrence masks to Boolean assignments. For 0 < ε ≤ 1, suppose two output laws are the exact uniform Bernoulli mixtures of out(mask) and out(mask with coordinate i forced false), respectively. Their Wasserstein distance is at most 1/ε times the integral from 1−ε to 1 of p times the expected Hamming distance between the outputs with i forced true and false. The proof uses a single shared finite mask seed and is the coupling bound in the source argument. Identifying the forced-absent output law with the platform law of the separately enumerated deleted multiset remains a separate obligation.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535, proof of Theorem 4.3, p. 17, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Definitions.Def_StabilityDichotomies_Approximability_Thinning
noncomputable section
open scoped Classical BigOperators Interval
open MeasureTheory StabilityDichotomies.Solvability

theorem StabilityDichotomies.Solvability.shared_mask_integrated_transport_bound (m : ℕ) {V : Type} [Fintype V]
    (out : (Fin m → Bool) → V → Bool) (i : Fin m) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (μ ν : PMF (V → Bool))
    (hμ : ∀ x, (μ x).toReal = ε⁻¹ * ∫ p in (1-ε)..1,
      ∑ mask : Fin m → Bool, retentionWeight p mask * (if out mask = x then 1 else 0))
    (hν : ∀ x, (ν x).toReal = ε⁻¹ * ∫ p in (1-ε)..1,
      ∑ mask : Fin m → Bool, retentionWeight p mask *
        (if out (Function.update mask i false) = x then 1 else 0)) :
    wasserstein μ ν ≤ ε⁻¹ * ∫ p in (1-ε)..1,
      p * ∑ mask : Fin m → Bool, retentionWeight p mask *
        (hammingDist (out (Function.update mask i true)) (out (Function.update mask i false)) : ℝ) := by sorry
