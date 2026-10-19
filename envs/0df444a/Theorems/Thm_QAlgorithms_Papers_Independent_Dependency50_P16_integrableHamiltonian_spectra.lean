-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_integrableHamiltonian_spectra
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.integrableHamiltonian_spectra
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:15:05.898349+00:00
-- url     : https://prove2.me/theorems/be62c08a-fcf2-47eb-8fe4-81dfb652a4d7
-- title:
--   Corollary 2.5: Spectra under integrable Hamiltonian control
-- statement:
--   Let $n\ge2$, let $G=-L$ be a finite-dimensional GKSL generator, and let $T\ge0$. Let $H:[0,T]\to i\mathfrak{su}(n)$ be an integrable traceless Hermitian Hamiltonian. If the normalized density path $\rho$ solves $\dot\rho=-i[H(t),\rho]-L(\rho)$ in the absolutely continuous, almost-everywhere sense, then its nonincreasing spectral path satisfies
--
--   $$\operatorname{spec}^{\downarrow}(\rho(\cdot))\text{ solves both (R) and (C).}$$
--
--   This is the forward spectral reduction for integrable Hamiltonian control.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 7, Corollary 2.5: Spectra under integrable Hamiltonian control

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P16

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ENNReal NNReal Matrix.Norms.L2Operator

open MeasureTheory Filter

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance 100] LieRing.ofAssociativeRing

namespace QAlgorithms.Papers.Independent.Dependency50.P16

local notation "Mat" => fun n : ℕ => Matrix (Fin n) (Fin n) ℂ

local notation "Vec" => fun n : ℕ => Fin n → ℝ

local notation "Hilbert" => fun n : ℕ => EuclideanSpace ℂ (Fin n)

local notation "Operator" => fun n : ℕ => Module.End ℂ (Mat n)

/-- arXiv:2308.00561v1, PDF p.7, Corollary 2.5: Spectra under integrable Hamiltonian control. The total spectral extension is evaluated only at normalized Hermitian density matrices. The zero-time interval imposes only its initial density. -/
theorem integrableHamiltonian_spectra {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n)
    (T : ℝ) (hT : 0 ≤ T) (H rho : ℝ → Mat n)
    (h : hamiltonianSolution D T H rho) :
    reducedSolution D (Set.Icc 0 T) (fun t => densitySpectrum (rho t)) ∧
      relaxedSolution D (Set.Icc 0 T) (fun t => densitySpectrum (rho t)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
