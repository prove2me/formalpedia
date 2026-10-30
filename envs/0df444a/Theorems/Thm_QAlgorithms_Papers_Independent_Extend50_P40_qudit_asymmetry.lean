-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P40_qudit_asymmetry
-- name    : QAlgorithms.Papers.Independent.Extend50.P40.qudit_asymmetry
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:06:40.655209+00:00
-- url     : https://prove2.me/theorems/dec16182-d2b4-4dfb-8a7a-81ef1baf9128
-- title:
--   §II.C.1 Eq.(29): optimal qudit asymmetric family
-- statement:
--   Let $d\ge2$, $a,b\ge0$, and $a^2+b^2+2ab/d=1$. The fixed directed modular-gate processor acts on the input and program $a\Phi_d+b|0\rangle|+_d\rangle$; it produces $a|\psi\rangle_A\Phi_{BM}+b|\psi\rangle_B\Phi_{AM}$ for all inputs. Its normalized single-copy marginals have fidelities
--
--   $$
--   F_A=1-\frac{d-1}{d}b^2,\qquad F_B=1-\frac{d-1}{d}a^2.
--   $$
--
--   These are optimal: no universal CPTP competitor with first fidelity at least F_A can have second fidelity larger than F_B. The processor is specified before the unknown input, including its modular subtraction gates.
-- source:
--   Quantum cloning, arXiv:quant-ph/0511088v1, PDF p. 11, §II.C.1 Eq.(29): optimal qudit asymmetric family

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

/-- II.C.1, PDF pp.10–11 Fig.2 and Eq.(29): fixed directed processor and program,
full marginal identities, and optimality of the nonnegative branch. -/
theorem qudit_asymmetry (d : ℕ) (hd : 2 ≤ d) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ^ 2 + b ^ 2 + 2 * a * b / d = 1) :
    (distributor d)ᴴ * distributor d = 1 ∧ ‖program d a b‖ = 1 ∧
    (∀ psi : EuclideanSpace ℂ (Fin d), ‖psi‖ = 1 →
      distributorOutput a b psi = asymmetricOutput a b psi ∧ ‖distributorOutput a b psi‖ = 1 ∧
      cloneMarginalA (distributorOutput a b psi) = depol (1 - b ^ 2) (pureDensity psi) ∧
      cloneMarginalB (distributorOutput a b psi) = depol (1 - a ^ 2) (pureDensity psi) ∧
      pureFidelity psi (cloneMarginalA (distributorOutput a b psi)) = 1 - ((d : ℝ) - 1) / d * b ^ 2 ∧
      pureFidelity psi (cloneMarginalB (distributorOutput a b psi)) = 1 - ((d : ℝ) - 1) / d * a ^ 2) ∧
    (∀ (T : Superop (Fin d) (Fin d × Fin d)) (fA fB : ℝ), IsChannel T →
      (∀ psi : EuclideanSpace ℂ (Fin d), ‖psi‖ = 1 →
        pureFidelity psi (traceRight (T (pureDensity psi))) = fA ∧
        pureFidelity psi (traceLeft (T (pureDensity psi))) = fB) →
      1 - ((d : ℝ) - 1) / d * b ^ 2 ≤ fA →
      fB ≤ 1 - ((d : ℝ) - 1) / d * a ^ 2) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P40

end
