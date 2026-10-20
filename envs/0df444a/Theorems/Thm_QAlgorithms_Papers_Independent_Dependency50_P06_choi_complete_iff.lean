-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P06_choi_complete_iff
-- name    : QAlgorithms.Papers.Independent.Dependency50.P06.choi_complete_iff
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:25:36.271234+00:00
-- url     : https://prove2.me/theorems/98e42f2e-f72b-4a9b-ba5e-c618d0c14ae1
-- title:
--   Choi criterion for complete CPTNI preservation
-- statement:
--   All quantum systems below have finite, nonzero dimension, with fixed orthonormal bases; one-dimensional systems are allowed. A channel system $A=(A_0,A_1)$ consists of an input and an output system, and likewise for $B$. A map is complex-linear on its full operator space. Density matrices are positive semidefinite with trace one. Write $A=A_0A_1$ and $B=B_0B_1$. Choi matrices use input-first order and the unnormalized vector $\sum_j|jj\rangle$. A missing subsystem in a superscript denotes its partial trace, and $T$ is plain transpose in the fixed basis. For an arbitrary supermap $\Theta:A\to B$,
--
--   $$\Theta\text{ is completely CPTNI-preserving}\quad\Longleftrightarrow\quad J_\Theta^{AB}\geq0\;\text{ and }\;\operatorname{Tr}[J_\Theta^{AB_0}(M^{AB_0})^T]\leq1$$
--
--   for every positive semidefinite $M^{AB_0}$ for which there exists a density matrix $\rho^{B_0}$ with $M^{A_0B_0}=I^{A_0}\otimes\rho^{B_0}$. The tests include all such matrices, including nonproduct ones. This is the complete normalization criterion used in the main characterization.
-- source:
--   Necessary and Sufficient Conditions on Measurements of Quantum Channels, arXiv:1904.09161v5, PDF p. 13, Appendix B.2; Eq. (4.2) (p.3)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P06

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Dependency50.P06

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22 (Op mixed)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

section QuantumResults

variable {A0 A1 B0 B1 : Type}

variable [Fintype A0] [Fintype A1] [Fintype B0] [Fintype B1]

variable [hA0 : Nonempty A0] [hA1 : Nonempty A1] [hB0 : Nonempty B0] [hB1 : Nonempty B1]

/-- PDF pp.3,12–13, (4.2): all positive testers with normalized marginal,
including entangled testers, characterize complete CPTNI preservation. -/
theorem choi_complete_iff (S : Supermap A0 A1 B0 B1) :
    IsCompletelyCPTNIPreserving S ↔ (superChoi S).PosSemidef ∧
      ∀ M : Op ((A0 × A1) × B0), IsTester M →
        (superMarginal (superChoi S) * M.transpose).trace.re ≤ 1 := by sorry

end QuantumResults

end QAlgorithms.Papers.Independent.Dependency50.P06

end
