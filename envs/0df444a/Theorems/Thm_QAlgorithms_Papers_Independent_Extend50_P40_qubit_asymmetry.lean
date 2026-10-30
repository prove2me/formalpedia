-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P40_qubit_asymmetry
-- name    : QAlgorithms.Papers.Independent.Extend50.P40.qubit_asymmetry
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:05:21.100027+00:00
-- url     : https://prove2.me/theorems/0df6259f-bfdc-484e-8f7d-a592aba4fde3
-- title:
--   §II.C Eq.(23) and Eqs.(24)–(28): sharp qubit asymmetric trade-off
-- statement:
--   Every universal qubit 1-to-2 CPTP cloner with common per-input fidelities $F_A,F_B$ satisfies the no-cloning trade-off. The fixed four-gate processor with program $a\Phi^++b|0+\rangle$, where $a,b\ge0$ and $a^2+b^2+ab=1$, attains
--
--   $$
--   \sqrt{(1-F_A)(1-F_B)}\ge\tfrac12-(1-F_A)-(1-F_B),\qquad F_A=1-b^2/2,\quad F_B=1-a^2/2.
--   $$
--
--   The displayed inequality is an equality on this branch. The actual marginal densities and normalization are included; identity, swap, and the symmetric 5/6 point are retained.
-- source:
--   Quantum cloning, arXiv:quant-ph/0511088v1, PDF p. 10, §II.C Eq.(23) and Eqs.(24)–(28): sharp qubit asymmetric trade-off

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

/-- II.C, PDF pp.10–11 Eqs.(23)–(28): all qubit competitors obey the bound;
nonnegative normalized programs attain it, including identity/swap and symmetric points. -/
theorem qubit_asymmetry :
    (∀ (T : Superop (Fin 2) (Fin 2 × Fin 2)) (fA fB : ℝ), IsChannel T →
      (∀ psi : EuclideanSpace ℂ (Fin 2), ‖psi‖ = 1 →
        pureFidelity psi (traceRight (T (pureDensity psi))) = fA ∧
        pureFidelity psi (traceLeft (T (pureDensity psi))) = fB) → QubitTradeoff fA fB) ∧
    (∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a ^ 2 + b ^ 2 + a * b = 1 →
      (distributor 2)ᴴ * distributor 2 = 1 ∧
      ∀ psi : EuclideanSpace ℂ (Fin 2), ‖psi‖ = 1 →
        distributorOutput a b psi = asymmetricOutput a b psi ∧ ‖distributorOutput a b psi‖ = 1 ∧
        cloneMarginalA (distributorOutput a b psi) = depol (1 - b ^ 2) (pureDensity psi) ∧
        cloneMarginalB (distributorOutput a b psi) = depol (1 - a ^ 2) (pureDensity psi) ∧
        pureFidelity psi (cloneMarginalA (distributorOutput a b psi)) = 1 - b ^ 2 / 2 ∧
        pureFidelity psi (cloneMarginalB (distributorOutput a b psi)) = 1 - a ^ 2 / 2 ∧
        Real.sqrt ((b ^ 2 / 2) * (a ^ 2 / 2)) = 1 / 2 - b ^ 2 / 2 - a ^ 2 / 2) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P40

end
