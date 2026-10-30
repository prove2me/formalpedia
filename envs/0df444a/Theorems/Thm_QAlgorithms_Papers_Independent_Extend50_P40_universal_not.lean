-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P40_universal_not
-- name    : QAlgorithms.Papers.Independent.Extend50.P40.universal_not
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:01:43.196186+00:00
-- url     : https://prove2.me/theorems/a7b4dd54-e9f0-4f64-95a3-6b9fc7c2527d
-- title:
--   §II.A.3 Eq.(15): optimal universal NOT from the ancilla
-- statement:
--   For a normalized qubit $\psi=(\alpha,\beta)$ put $\psi^\perp=(-\overline\beta,\overline\alpha)$. The Buzek–Hillery machine marginal is also produced by random-basis measurement followed by preparation of the opposite outcome, and
--
--   $$
--   \rho_M=\tfrac23|\psi^\perp\rangle\langle\psi^\perp|+\tfrac13|\psi\rangle\langle\psi|,\qquad F_{\rm NOT}=\tfrac23.
--   $$
--
--   Every CPTP NOT approximator with constant pure-target fidelity has fidelity at most 2/3. Perfect universal NOT is impossible. The target is the orthogonal state, not the original.
-- source:
--   Quantum cloning, arXiv:quant-ph/0511088v1, PDF p. 8, §II.A.3 Eq.(15): optimal universal NOT from the ancilla

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P40

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P40

open QAlgorithms

open scoped Matrix ComplexOrder ComplexConjugate BigOperators Topology

open MeasureTheory Filter

open scoped Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P12 (sigma)

open QAlgorithms.Papers.Independent.Dependency50.P48 (pureFidelity)

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Support21.P16
  (CloneMap IsBoseInputChannel coherentTensor tensorWithIdentity canonicalCloner
   HasBoseOutput HasBlackCowCoefficient canonicalCoefficient oneMixed)

open QAlgorithms.Papers.Independent.Renew46.P45
  (TensorMat boseProjector siteObservable)

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

/-- II.A.3, PDF p.8 Eq.(15): the machine output is the optimal universal anti-clone.
The target is psi_perp. The perfect NOT cannot be a channel; optimal 2/3 is attainable. -/
theorem universal_not :
    IsChannel measureNot ∧
    (∀ psi : EuclideanSpace ℂ (Fin 2), ‖psi‖ = 1 →
      measureNot (pureDensity psi) = marginalMachine (bhOutput psi)) ∧
    (∀ psi : EuclideanSpace ℂ (Fin 2), ‖psi‖ = 1 →
      marginalMachine (bhOutput psi) =
        (2 / 3 : ℂ) • pureDensity (orthogonalQubit psi) + (1 / 3 : ℂ) • pureDensity psi ∧
      pureFidelity (orthogonalQubit psi) (marginalMachine (bhOutput psi)) = 2 / 3) ∧
    (∀ (T : Superop (Fin 2) (Fin 2)) (f : ℝ), IsChannel T →
      (∀ psi : EuclideanSpace ℂ (Fin 2), ‖psi‖ = 1 → pureFidelity (orthogonalQubit psi) (T (pureDensity psi)) = f) → f ≤ 2 / 3) ∧
    (¬ ∃ T : Superop (Fin 2) (Fin 2), IsChannel T ∧
      ∀ psi : EuclideanSpace ℂ (Fin 2), ‖psi‖ = 1 → T (pureDensity psi) = pureDensity (orthogonalQubit psi)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P40

end
