-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P40_lemma4_sl_linear
-- name    : QAlgorithms.Papers.Independent.Advance50.P40.lemma4_sl_linear
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T09:04:34.343835+00:00
-- url     : https://prove2.me/theorems/5f7833f4-6a6a-4058-8091-3707990f9d76
-- title:
--   Lemma 4: the specified SL extension is complex-linear and matches the QDP
-- statement:
--   Fix positive integers $n,m$ and fixed orthonormal system and bath coordinates. Write $M_n$ for the complex system matrices, $E_{ij}=|i\rangle\langle j|$, and let $\phi_{ij}\in M_m$ be fixed bath operators with $\phi_{ji}=\phi_{ij}^{\dagger}$ and, for each $i,j$, either $\phi_{ij}=0$ or $\operatorname{Tr}\phi_{ij}=1$. Define
--   $$
--   \mathcal A_\phi(X)=\sum_{i,j}X_{ij}E_{ij}\otimes\phi_{ij},\qquad
--   \Phi_{U,\phi}(X)=\operatorname{Tr}_B\bigl[U\mathcal A_\phi(X)U^{\dagger}\bigr].
--   $$
--   Here $U$ is a joint unitary and the bath is the second tensor factor. A scalar matrix $R$ is admissible when it is Hermitian, $\sum_i R_{ii}=1$, and $\mathcal A_\phi(R)$ is a positive semidefinite trace-one matrix. Zero bath operators annihilate their corresponding matrix units on every input.
--
--   For every such $U$ there is one complex-linear map $F:M_n\to M_n$ satisfying
--   $$
--   F(X)=\Phi_{U,\phi}(X)\quad(X\in M_n),
--   $$
--   and, simultaneously for every admissible $R$,
--   $$
--   F\!\left(\operatorname{Tr}_B\mathcal A_\phi(R)\right)
--   =\operatorname{Tr}_B\bigl[U\mathcal A_\phi(R)U^{\dagger}\bigr].
--   $$
--   This supplies the linearity and physical input-output agreement underlying Theorem 2.
-- source:
--   Vanishing quantum discord is necessary and sufficient for completely positive maps, arXiv:0808.0175v2, PDF p. 4, Lemma 4

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P40

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P40

/-- Lemma 4, PDF p. 4: the fixed matrix-unit extension is complex-linear and
reproduces Eq. (1) for every admissible SL initial state. -/
theorem lemma4_sl_linear {n m : ℕ} [NeZero n] [NeZero m]
    (phi : BathFamily n m) (hphi : IsSLFamily phi)
    (U : Matrix.unitaryGroup (Fin n × Fin m) ℂ) :
    ∃ F : SystemMatrix n →ₗ[ℂ] SystemMatrix n,
      (∀ X, F X = specifiedReducedMap phi U X) ∧
      ∀ R, IsSLAdmissibleInput phi R →
        F (QAlgorithms.traceRight (sourceAssignment phi R)) =
          qdp U (sourceAssignment phi R) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P40

end
