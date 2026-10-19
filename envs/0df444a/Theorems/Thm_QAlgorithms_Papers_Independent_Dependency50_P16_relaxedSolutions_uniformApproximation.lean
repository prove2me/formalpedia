-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_relaxedSolutions_uniformApproximation
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.relaxedSolutions_uniformApproximation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:46:11.968975+00:00
-- url     : https://prove2.me/theorems/6884d705-9797-483a-875d-d2877f9fa25b
-- title:
--   Unnumbered relaxation theorem
-- statement:
--   For a GKSL generator on $\mathbb C^n$, $n\ge2$, every solution $\lambda$ of (C) on a compact interval $[0,T]$, $T\ge0$, can be approximated by solutions of (R) with the same initial state:
--
--   $$\forall\varepsilon>0\ \exists\lambda_\varepsilon\text{ solving (R)}:\quad\lambda_\varepsilon(0)=\lambda(0),\quad\sup_{0\le t\le T}\|\lambda_\varepsilon(t)-\lambda(t)\|\le\varepsilon.$$
--
--   This asserts uniform density of reduced trajectories in relaxed trajectories on compact time intervals, rather than equality of solution sets.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 7, Unnumbered relaxation theorem

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

/-- arXiv:2308.00561v1, PDF p.7, Unnumbered relaxation theorem. The initial state is fixed as in the section systems. All norms on this finite-dimensional space induce the same uniform approximation notion. -/
theorem relaxedSolutions_uniformApproximation {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n)
    (T : ℝ) (hT : 0 ≤ T) (path : ℝ → Vec n)
    (hpath : relaxedSolution D (Set.Icc 0 T) path) :
    ∀ eps : ℝ, 0 < eps → ∃ approx : ℝ → Vec n,
      reducedSolution D (Set.Icc 0 T) approx ∧ approx 0 = path 0 ∧
        ∀ t ∈ Set.Icc 0 T, ‖approx t - path t‖ ≤ eps := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
