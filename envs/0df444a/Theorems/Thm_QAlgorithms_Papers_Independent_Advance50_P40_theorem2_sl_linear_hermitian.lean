-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P40_theorem2_sl_linear_hermitian
-- name    : QAlgorithms.Papers.Independent.Advance50.P40.theorem2_sl_linear_hermitian
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T09:01:26.602901+00:00
-- url     : https://prove2.me/theorems/ffd8f3de-310f-44d9-9c0f-cc594492bf15
-- title:
--   Theorem 2: fixed SL data give a linear Hermitian reduced map
-- statement:
--   Fix positive integers $n,m$ and fixed orthonormal system and bath coordinates. Write $M_n$ for the complex system matrices, $E_{ij}=|i\rangle\langle j|$, and let $\phi_{ij}\in M_m$ be fixed bath operators with $\phi_{ji}=\phi_{ij}^{\dagger}$ and, for each $i,j$, either $\phi_{ij}=0$ or $\operatorname{Tr}\phi_{ij}=1$. Define
--   $$
--   \mathcal A_\phi(X)=\sum_{i,j}X_{ij}E_{ij}\otimes\phi_{ij},\qquad
--   \Phi_{U,\phi}(X)=\operatorname{Tr}_B\bigl[U\mathcal A_\phi(X)U^{\dagger}\bigr].
--   $$
--   Here $U$ is a joint unitary and the bath is the second tensor factor. A scalar matrix $R$ is admissible when it is Hermitian, $\sum_i R_{ii}=1$, and $\mathcal A_\phi(R)$ is a positive semidefinite trace-one matrix. Zero bath operators annihilate their corresponding matrix units on every input.
--
--   For every such $U$ there is one complex-linear map $F:M_n\to M_n$, chosen before the admissible scalar input, with
--   $$
--   F(X)=\Phi_{U,\phi}(X)\quad(X\in M_n),\qquad
--   X=X^{\dagger}\Longrightarrow F(X)=F(X)^{\dagger},
--   $$
--   and, for every admissible $R$,
--   $$
--   F\!\left(\operatorname{Tr}_B\mathcal A_\phi(R)\right)
--   =\operatorname{Tr}_B\bigl[U\mathcal A_\phi(R)U^{\dagger}\bigr].
--   $$
--   This identifies a single Hermiticity-preserving extension for the entire compatible SL family.
-- source:
--   Vanishing quantum discord is necessary and sufficient for completely positive maps, arXiv:0808.0175v2, PDF p. 2, Theorem 2

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P40

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P40

/-- Theorem 2, PDF p. 2, with the explicit extension from Eqs. (14)-(15),
PDF p. 4. The same complex-linear Hermiticity-preserving map acts correctly
on every admissible marginal for the fixed coefficient family and joint unitary. -/
theorem theorem2_sl_linear_hermitian {n m : ℕ} [NeZero n] [NeZero m]
    (phi : BathFamily n m) (hphi : IsSLFamily phi)
    (U : Matrix.unitaryGroup (Fin n × Fin m) ℂ) :
    ∃ F : SystemMatrix n →ₗ[ℂ] SystemMatrix n,
      (∀ X, F X = specifiedReducedMap phi U X) ∧
      (∀ X, X.IsHermitian → (F X).IsHermitian) ∧
      ∀ R, IsSLAdmissibleInput phi R →
        F (QAlgorithms.traceRight (sourceAssignment phi R)) =
          qdp U (sourceAssignment phi R) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P40

end
