-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P40_proposition1_zero_diagonal
-- name    : QAlgorithms.Papers.Independent.Advance50.P40.proposition1_zero_diagonal
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T09:02:35.623168+00:00
-- url     : https://prove2.me/theorems/62a61f4e-b83f-474f-8d01-813cd6fda111
-- title:
--   Proposition 1: a zero bath diagonal annihilates its connected off-diagonal pair
-- statement:
--   Fix positive integers $n,m$ and fixed orthonormal system and bath coordinates. Write $M_n$ for the complex system matrices, $E_{ij}=|i\rangle\langle j|$, and let $\phi_{ij}\in M_m$ be fixed bath operators with $\phi_{ji}=\phi_{ij}^{\dagger}$ and, for each $i,j$, either $\phi_{ij}=0$ or $\operatorname{Tr}\phi_{ij}=1$. Define
--   $$
--   \mathcal A_\phi(X)=\sum_{i,j}X_{ij}E_{ij}\otimes\phi_{ij},\qquad
--   \Phi_{U,\phi}(X)=\operatorname{Tr}_B\bigl[U\mathcal A_\phi(X)U^{\dagger}\bigr].
--   $$
--   Here $U$ is a joint unitary and the bath is the second tensor factor. A scalar matrix $R$ is admissible when it is Hermitian, $\sum_i R_{ii}=1$, and $\mathcal A_\phi(R)$ is a positive semidefinite trace-one matrix. Zero bath operators annihilate their corresponding matrix units on every input.
--
--    Assume that the same fixed family $\phi$ has the following property: for every joint unitary $U$, the map $\Phi_{U,\phi}$ is completely positive on all system matrices. Fix an admissible $R$; this retains the initial-state setting of the enclosing necessity proof. Complete positivity here does not require trace preservation. For distinct system indices $k,l$,
--   $$
--   \phi_{kk}=0\ \text{or}\ \phi_{ll}=0
--   \quad\Longrightarrow\quad \phi_{kl}=0\ \text{and}\ \phi_{lk}=0.
--   $$
--   This is the zero-diagonal restriction used to analyze the coefficient blocks in the CP necessity proof.
-- source:
--   Vanishing quantum discord is necessary and sufficient for completely positive maps, arXiv:0808.0175v2, PDF p. 3, Proposition 1

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P40

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P40

/-- Proposition 1, PDF p. 3, in the all-unitary CP necessity proof of Lemma 1.
The scalar input witnesses the standing SL density-state setting. -/
theorem proposition1_zero_diagonal {n m : ℕ} [NeZero n] [NeZero m]
    (phi : BathFamily n m) (hphi : IsSLFamily phi)
    (R : SystemMatrix n) (hR : IsSLAdmissibleInput phi R) (hcp : AllUnitaryCP phi)
    (k l : Fin n) (hkl : k ≠ l) (hzero : phi k k = 0 ∨ phi l l = 0) :
    phi k l = 0 ∧ phi l k = 0 := by sorry

end QAlgorithms.Papers.Independent.Advance50.P40

end
