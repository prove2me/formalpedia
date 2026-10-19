-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_closedReachable_contractible
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.closedReachable_contractible
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:21:48.272615+00:00
-- url     : https://prove2.me/theorems/2b35e32f-a12f-4724-a202-802b0d072e30
-- title:
--   Proposition 4.2: Contractible closed reachable set
-- statement:
--   Let $G=-L$ be a GKSL generator on $\mathbb C^n$, $n\ge2$, which is not purely Hamiltonian, and let $\lambda\in\Delta^{n-1}$. Then
--
--   $$\frac en\in\overline{\operatorname{reach}_C(\lambda)},\qquad\overline{\operatorname{reach}_C(\lambda)}\text{ is contractible}.$$
--
--   The closure is of the all-time reachable set; finite-time exact attainment of the barycenter is not asserted.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 13, Proposition 4.2: Contractible closed reachable set

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

/-- arXiv:2308.00561v1, PDF p.13, Proposition 4.2: Contractible closed reachable set. The topology is the subtype topology of the closed all-time spectral reachable set. -/
theorem closedReachable_contractible {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n)
    (x : Vec n) (hx : x ∈ simplex n) (h : ¬purelyHamiltonian D) :
    barycenter n ∈ closure (reachC D x) ∧ ContractibleSpace (closure (reachC D x)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
