-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P06_tester_realization
-- name    : QAlgorithms.Papers.Independent.Dependency50.P06.tester_realization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:23:17.333912+00:00
-- url     : https://prove2.me/theorems/9f6d6cdf-e94d-4f71-8745-aa2c86ca5269
-- title:
--   Every admissible positive tester has a channel-and-state realization
-- statement:
--   All quantum systems below have finite, nonzero dimension, with fixed orthonormal bases; one-dimensional systems are allowed. A channel system $A=(A_0,A_1)$ consists of an input and an output system, and likewise for $B$. A map is complex-linear on its full operator space. Density matrices are positive semidefinite with trace one. Write $A=A_0A_1$ and $B=B_0B_1$. Choi matrices use input-first order and the unnormalized vector $\sum_j|jj\rangle$. A missing subsystem in a superscript denotes its partial trace, and $T$ is plain transpose in the fixed basis. Let $M^{AB_0}\geq0$ and let $\rho^{B_0}$ be any density matrix, including a singular one, such that $M^{A_0B_0}=I^{A_0}\otimes\rho^{B_0}$. There exist finite nonzero systems $R_0,R_1$, a channel $N:R_0A_0\to R_1A_1$, and a density matrix $\sigma^{R_0B_0}$ such that
--
--   $$M^{AB_0}=\operatorname{Tr}_{R_0}\!\left[(\sigma^{R_0B_0}\otimes I^A)\bigl((J_N^{R_0A})^{T_{R_0}}\otimes I^{B_0}\bigr)\right].$$
--
--   Here $J_N^{R_0A}=\operatorname{Tr}_{R_1}J_N$; the inner transpose is partial on $R_0$, and the outer trace is only over $R_0$, with factors reindexed as displayed. This realizes every tester needed in the complete Choi criterion.
-- source:
--   Necessary and Sufficient Conditions on Measurements of Quantum Channels, arXiv:1904.09161v5, PDF p. 12, Lemma B.1

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

/-- PDF pp.12–13, Lemma B.1: every positive tester has the specified linked
realization. Ancillas, channel and joint density matrix are conclusions. -/
theorem tester_realization [Nonempty A0] [Nonempty A1] [Nonempty B0] (M : Op ((A0 × A1) × B0)) (hM : M.PosSemidef)
    (rho : Op B0) (hrho : IsDensityMatrix rho)
    (hmarg : testerMarginal M = Matrix.kronecker (1 : Op A0) rho) :
    ∃ r0 r1 : ℕ, 0 < r0 ∧ 0 < r1 ∧
      ∃ N : QMap (Fin r0 × A0) (Fin r1 × A1), IsChannel N ∧
        ∃ sigma : Op (Fin r0 × B0), IsDensityMatrix sigma ∧ M = linkedTester N sigma := by sorry

end QuantumResults

end QAlgorithms.Papers.Independent.Dependency50.P06

end
