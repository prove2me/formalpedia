-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P06_choi_cptni_iff
-- name    : QAlgorithms.Papers.Independent.Dependency50.P06.choi_cptni_iff
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:24:37.59802+00:00
-- url     : https://prove2.me/theorems/1fcd17fb-490e-402f-a327-eb002e53c30c
-- title:
--   Choi criterion for ordinary CPTNI preservation
-- statement:
--   All quantum systems below have finite, nonzero dimension, with fixed orthonormal bases; one-dimensional systems are allowed. A channel system $A=(A_0,A_1)$ consists of an input and an output system, and likewise for $B$. A map is complex-linear on its full operator space. Density matrices are positive semidefinite with trace one. Write $A=A_0A_1$ and $B=B_0B_1$. Choi matrices use input-first order and the unnormalized vector $\sum_j|jj\rangle$. A missing subsystem in a superscript denotes its partial trace, and $T$ is plain transpose in the fixed basis. For an arbitrary supermap $\Theta:A\to B$,
--
--   $$\Theta\text{ is CPTNI-preserving}\quad\Longleftrightarrow\quad J_\Theta^{AB}\geq0\;\text{ and }\;\operatorname{Tr}[J_\Theta^{AB_0}(J_N^A\otimes\rho^{B_0})^T]\leq1$$
--
--   for every channel $N:A_0\to A_1$ and every density matrix $\rho^{B_0}$. This is the product-tester characterization of ordinary preservation.
-- source:
--   Necessary and Sufficient Conditions on Measurements of Quantum Channels, arXiv:1904.09161v5, PDF p. 3, Eq. (4.1); Appendix B.1 (p.11)

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

/-- PDF pp.3,11, (4.1): Choi positivity and all product channel/state tests
characterize CPTNI preservation. AB0 denotes the B1 marginal. -/
theorem choi_cptni_iff (S : Supermap A0 A1 B0 B1) :
    IsCPTNIPreserving S ↔ (superChoi S).PosSemidef ∧
      ∀ (N : QMap A0 A1), IsChannel N → ∀ rho : Op B0, IsDensityMatrix rho →
        (superMarginal (superChoi S) * (Matrix.kronecker (choi N) rho).transpose).trace.re ≤ 1 := by sorry

end QuantumResults

end QAlgorithms.Papers.Independent.Dependency50.P06

end
