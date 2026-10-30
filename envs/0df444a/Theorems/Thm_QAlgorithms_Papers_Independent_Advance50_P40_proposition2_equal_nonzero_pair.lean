-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P40_proposition2_equal_nonzero_pair
-- name    : QAlgorithms.Papers.Independent.Advance50.P40.proposition2_equal_nonzero_pair
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:03:16.691578+00:00
-- url     : https://prove2.me/theorems/0e9806df-6cdb-4e9a-b590-8da0040be3e1
-- title:
--   Proposition 2: a nonzero pair has four equal bath coefficients
-- statement:
--   Fix positive integers $n,m$ and fixed orthonormal system and bath coordinates. Write $M_n$ for the complex system matrices, $E_{ij}=|i\rangle\langle j|$, and let $\phi_{ij}\in M_m$ be fixed bath operators with $\phi_{ji}=\phi_{ij}^{\dagger}$ and, for each $i,j$, either $\phi_{ij}=0$ or $\operatorname{Tr}\phi_{ij}=1$. Define
--   $$
--   \mathcal A_\phi(X)=\sum_{i,j}X_{ij}E_{ij}\otimes\phi_{ij},\qquad
--   \Phi_{U,\phi}(X)=\operatorname{Tr}_B\bigl[U\mathcal A_\phi(X)U^{\dagger}\bigr].
--   $$
--   Here $U$ is a joint unitary and the bath is the second tensor factor. A scalar matrix $R$ is admissible when it is Hermitian, $\sum_i R_{ii}=1$, and $\mathcal A_\phi(R)$ is a positive semidefinite trace-one matrix. Zero bath operators annihilate their corresponding matrix units on every input.
--
--    Assume that the same fixed family $\phi$ has the following property: for every joint unitary $U$, the map $\Phi_{U,\phi}$ is completely positive on all system matrices. Fix an admissible $R$; this retains the initial-state setting of the enclosing necessity proof. Complete positivity here does not require trace preservation. Let $k\ne l$ satisfy $\phi_{kk}\ne0$, $\phi_{ll}\ne0$, and $\phi_{kl}\ne0$. Then
--   $$
--   \phi_{kk}=\phi_{ll}=\phi_{kl}=\phi_{lk}.
--   $$
--   This constrains each nonzero connection in the coefficient graph and supplies the local equality used in the block decomposition.
-- source:
--   Vanishing quantum discord is necessary and sufficient for completely positive maps, arXiv:0808.0175v2, PDF p. 3, Proposition 2

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P40

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P40

/-- Proposition 2, PDF p. 3, with the inherited all-unitary CP hypothesis.
All four named operators are identified; no spectral typo is used as a hypothesis. -/
theorem proposition2_equal_nonzero_pair {n m : ℕ} [NeZero n] [NeZero m]
    (phi : BathFamily n m) (hphi : IsSLFamily phi)
    (R : SystemMatrix n) (hR : IsSLAdmissibleInput phi R) (hcp : AllUnitaryCP phi)
    (k l : Fin n) (hkl : k ≠ l)
    (hkk : phi k k ≠ 0) (hll : phi l l ≠ 0) (hpair : phi k l ≠ 0) :
    phi k k = phi l l ∧ phi l l = phi k l ∧ phi k l = phi l k := by sorry

end QAlgorithms.Papers.Independent.Advance50.P40

end
