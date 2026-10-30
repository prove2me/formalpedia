-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P37_qubit_phase_simulation
-- name    : QAlgorithms.Papers.Independent.Extend50.P37.qubit_phase_simulation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:29:18.646303+00:00
-- url     : https://prove2.me/theorems/72e9966a-fc92-4408-aa17-ab1e1d2dec39
-- title:
--   IV B 3: explicit classical simulation for two phase-symmetric qubits
-- statement:
--   Let $H_2$ be the scalar-extended number-phase group on a qubit. For every $n\ge1$ and each sign, any globally $H_2$-symmetric arbitrary-outcome POVM has a locally diagonal simulator with the same statistics on all states supported in that permutation sector.
--
--   For two qubits in the symmetric sector the simulator is explicit:
--   $$\widetilde M(B)=\sum_{z\in\{00,01,10,11\}}\operatorname{tr}(M(B)\tau_z)|z\rangle\langle z|,$$
--   where $\tau_{00}=|00\rangle\langle00|$, $\tau_{11}=|11\rangle\langle11|$, and $\tau_{01}=\tau_{10}=|\phi_+\rangle\langle\phi_+|$ with $|\phi_+\rangle=(|01\rangle+|10\rangle)/\sqrt2$. This is a fixed computational-basis measurement followed by classical processing.
-- source:
--   A generalization of Schur-Weyl duality with applications in quantum estimation, arXiv:1112.0638v3, PDF p. 16, IV B 3: explicit classical simulation for two phase-symmetric qubits

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P37

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P37

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Next46.P29 (phaseAverage)

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P37.estimationMatrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P37.estimationMatrixBorel

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- PDF pp.15-17, IV B 3: simulation for arbitrary copy number and both signs,
plus the explicit p.16 kernel in the symmetric two-qubit sector. -/
theorem qubit_phase_simulation {O : Type*} [MeasurableSpace O] :
    (∀ n : ℕ, 0 < n → ∀ s : Bool,
      ∀ M : Measurements.OperatorPOVM (Fin n → Fin 2) O,
        InAlgebra M.operator (Set.centralizer (collectiveImage n (phaseGroup 2))) →
        ∃ N : Measurements.OperatorPOVM (Fin n → Fin 2) O,
          InAlgebra N.operator (tensorAlg n (diagonalSet (Fin 2))) ∧
          ∀ rho, IsDensityMatrix rho → permutationSector (Fin 2) n s * rho * permutationSector (Fin 2) n s = rho →
            ∀ B, MeasurableSet B → effectProb (M.operator B) rho = effectProb (N.operator B) rho) ∧
    (∀ M : Measurements.OperatorPOVM (Fin 2 → Fin 2) O,
      InAlgebra M.operator (Set.centralizer (collectiveImage 2 (phaseGroup 2))) →
      ∃ N : Measurements.OperatorPOVM (Fin 2 → Fin 2) O,
        (∀ B, MeasurableSet B → N.operator B =
          ∑ z : Fin 2 → Fin 2, (effectProb (M.operator B) (qubitFilling false z) : ℂ) •
            pureDensity (pairBasisKet 2 (z 0) (z 1))) ∧
        ∀ rho, IsDensityMatrix rho →
          permutationSector (Fin 2) 2 false * rho * permutationSector (Fin 2) 2 false = rho →
          ∀ B, MeasurableSet B → effectProb (M.operator B) rho = effectProb (N.operator B) rho) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P37

end
