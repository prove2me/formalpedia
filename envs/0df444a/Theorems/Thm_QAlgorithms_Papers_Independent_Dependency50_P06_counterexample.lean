-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P06_counterexample
-- name    : QAlgorithms.Papers.Independent.Dependency50.P06.counterexample
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:21:16.434991+00:00
-- url     : https://prove2.me/theorems/7299c6f4-c4fc-4459-b40f-09e7b39f9883
-- title:
--   Explicit CPTNI-preserving supermap that fails complete preservation
-- statement:
--   All quantum systems below have finite, nonzero dimension, with fixed orthonormal bases; one-dimensional systems are allowed. A channel system $A=(A_0,A_1)$ consists of an input and an output system, and likewise for $B$. A map is complex-linear on its full operator space. Density matrices are positive semidefinite with trace one. Write $A=A_0A_1$ and $B=B_0B_1$. Choi matrices use input-first order and the unnormalized vector $\sum_j|jj\rangle$. A missing subsystem in a superscript denotes its partial trace, and $T$ is plain transpose in the fixed basis. For four qubits let $u=I/2$, $Y=\begin{pmatrix}0&-i\\i&0\end{pmatrix}$, $|\psi_-\rangle=(|01\rangle-|10\rangle)/\sqrt2$, and $P_-=|\psi_-\rangle\langle\psi_-|$. Construct $\Theta$ by $J_\Theta=I^{A_0}\otimes P_-^{A_1B_0}\otimes u^{B_1}$. Its action, on every linear map $E$ and every operator $X$ on $B_0$, is
--
--   $$\Theta[E](X)=\operatorname{Tr}\!\left[E(u)(YXY)^T\right]u.$$
--
--   Here $A_1$ is identified with $B_0$ in the stated basis. This supermap is CPP and CPTNI-preserving, but is not completely CPTNI-preserving. Explicitly, $M=(J_\Theta^{AB_0})^T$ is positive semidefinite, has marginal $I^{A_0}\otimes u^{B_0}$, and satisfies $\operatorname{Tr}[J_\Theta^{AB_0}M^T]=2>1$. The construction witnesses a strict distinction between ordinary and complete CPTNI preservation.
-- source:
--   Necessary and Sufficient Conditions on Measurements of Quantum Channels, arXiv:1904.09161v5, PDF p. 13, Appendix C; Eq. (2.4) (p.2)

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

/-- PDF pp.2,13–15, (2.4) and Appendix C: all-qubit counterexample, its action,
and its explicit admissible tester with value 2. -/
theorem counterexample :
    IsCPP (counterSupermap (Fin 2)) ∧
    IsCPTNIPreserving (counterSupermap (Fin 2)) ∧
    ¬ IsCompletelyCPTNIPreserving (counterSupermap (Fin 2)) ∧
    superChoi (counterSupermap (Fin 2)) = counterChoi (Fin 2) ∧
    IsTester counterTester ∧
    (superMarginal (counterChoi (Fin 2)) * counterTester.transpose).trace.re = 2 ∧
    ∀ (N : QMap (Fin 2) (Fin 2)) (X : Op (Fin 2)),
      superApply (counterSupermap (Fin 2)) N X =
        (N (mixed (Fin 2)) * (pauliY * X * pauliY).transpose).trace • mixed (Fin 2) := by sorry

end QuantumResults

end QAlgorithms.Papers.Independent.Dependency50.P06

end
