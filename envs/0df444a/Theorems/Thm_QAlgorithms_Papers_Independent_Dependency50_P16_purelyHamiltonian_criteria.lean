-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_purelyHamiltonian_criteria
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.purelyHamiltonian_criteria
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:34:35.065279+00:00
-- url     : https://prove2.me/theorems/3bfe6c4b-462c-4c51-b230-f7ed353b50c2
-- title:
--   Lemma 5.8: Purely Hamiltonian systems
-- statement:
--   For a GKSL generator $G=-L$ on $\mathbb C^n$, $n\ge2$, the following are equivalent: $L=i[H,\cdot]$ for some Hermitian $H$; every eigenvalue of the superoperator $G$ lies on the imaginary axis; every jump is scalar in some, equivalently every, representation; every nonzero complex linear subspace is lazy; and
--
--   $$\forall U\in SU(n),\quad J(U)\text{ is diagonal}\quad\Longleftrightarrow\quad L_U=0.$$
--
--   These characterize purely Hamiltonian systems. The superoperator eigenvalue clause quantifies nonzero eigenmatrices, rather than eigenvalues of the drift or individual jumps.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 25, Lemma 5.8: Purely Hamiltonian systems

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

/-- arXiv:2308.00561v1, PDF p.25, Lemma 5.8: Purely Hamiltonian systems. The zero subspace is invariant but is not named lazy. Arbitrary finite jump counts, including zero, are allowed. Superoperator eigenvectors are matrices X != 0. -/
theorem purelyHamiltonian_criteria {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n) :
    List.TFAE [purelyHamiltonian D,
      (∀ z : ℂ, (∃ X : Mat n, X ≠ 0 ∧ gkslGenerator D X = z • X) → z.re = 0),
      someRepresentation D (fun E => ∀ k, ∃ c : ℂ, E.jump k = c • (1 : Mat n)),
      everyRepresentation D (fun E => ∀ k, ∃ c : ℂ, E.jump k = c • (1 : Mat n)),
      (∀ S : Submodule ℂ (Hilbert n), S ≠ ⊥ → lazy D.jump S),
      (∀ U, specialUnitary U → ∀ i j, i ≠ j → rates D.jump U i j = 0),
      (∀ U, specialUnitary U → populationGenerator D.jump U = 0)] := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
