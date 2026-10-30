-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P09_unconstrained_haar
-- name    : QAlgorithms.Papers.Independent.Extend50.P09.unconstrained_haar
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:31:41.384299+00:00
-- url     : https://prove2.me/theorems/b4b11c2e-ebed-4564-8075-c97fdcb9889a
-- title:
--   §VI: no-symmetry Choi decoupling comparison
-- statement:
--   Encode $k$ logical qubits into $n$ physical qubits by appending a fixed normalized pure $(n-k)$-qubit ancilla and applying a full Haar unitary, with no symmetry constraint. Erase a fixed known set of $t$ sites, where $0\le k,t\le n$ and $\Delta=n-k-4t\ge0$. The Choi error is the optimal CPTP recovery purified distance on a normalized maximally entangled input. There are absolute $C,c>0$ and $\Delta_0$ such that uniformly over these data, for $\Delta\ge\Delta_0$,
--   $$\mathbb E\epsilon_{\rm Choi}\le C e^{-c\Delta}.$$
--
--   Exponential decay in $n$ follows only with a linear gap $\Delta=\Omega(n)$; no worst-case-error conclusion is added.
-- source:
--   Near-optimal covariant quantum error-correcting codes from random unitaries with symmetries, arXiv:2112.01498v2, PDF p. 13, §VI: no-symmetry Choi decoupling comparison

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P09

noncomputable section

open scoped Matrix Matrix.Norms.Elementwise ComplexConjugate ENNReal ComplexOrder

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Extend50.P09

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact generic definitions from the pinned accepted library.

open QAlgorithms.Papers.Independent.Information100.P22 (Op mixed bell)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalMinEntropy)

open QAlgorithms.Papers.Independent.Advance50.P02 (negLog)

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P09.covariantMatrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P09.covariantMatrixBorel

/-- §VI, PDF pp.13–14: expected Choi error decays exponentially in
Delta=n-k-4t. Merely nonnegative Delta does not imply exponential decay in n.
The source's numerical gap is retained without naming it the sharp Singleton bound. -/
theorem unconstrained_haar (laws : PhysicalUnitaryLaws 2)
    (hlaw : ∀ n, IsCommutantHaarLaw (FullGroup 2 n) (laws n)) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ delta0 : ℕ,
    ∀ n k t : ℕ, ∀ h : k ≤ n, k+4*t ≤ n → delta0 ≤ n-k-4*t →
    ∀ psi : EuclideanSpace ℂ (CovariantWord 2 (n-k)), IsState psi →
    ∀ S : Finset (Fin n), S.card = t →
    (∫ U, choiError (noisyEncoder h (pureDensity psi) S U) ∂laws n) ≤
      C * Real.exp (-c*((n : ℝ)-k-4*t)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P09

end
