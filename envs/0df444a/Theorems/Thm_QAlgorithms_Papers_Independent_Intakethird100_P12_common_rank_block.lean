-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P12_common_rank_block
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P12.common_rank_block
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:48:15.245991+00:00
-- url     : https://prove2.me/theorems/3c1a2517-a55a-4d44-8a45-780b96e33c74
-- title:
--   Proposition 2.1: common rank-block representation and midpoint summands
-- statement:
--   Let $\rho$ be a complex positive semidefinite matrix of order $n$, with actual rank $k<n$. Define $B_A(L)=\begin{pmatrix}L&LA\\A^\dagger L&A^\dagger LA\end{pmatrix}$, where $A$ has size $k\times(n-k)$ and $L$ has order $k$. There exist a permutation unitary $\sigma$, such a matrix $A$, and a strictly positive definite matrix $K$ of order $k$ for which
--   $$\sigma\rho\sigma^{-1}=B_A(K).$$
--   The same $\sigma,A$ work for every decomposition $\rho=\tfrac12(\rho'+\rho'')$ into positive semidefinite matrices: there exist positive semidefinite matrices $K',K''$ of order $k$ such that
--   $$\sigma\rho'\sigma^{-1}=B_A(K'),\qquad\sigma\rho''\sigma^{-1}=B_A(K'').$$
--   This common representation controls midpoint decompositions even when their summands are singular. No trace normalization is imposed; $k=0$ is allowed. The source's unqualified “positive definite” means positive semidefinite, as its Gram-matrix proof confirms.
-- source:
--   Extremal Quantum States in Coupled Systems, arXiv:quant-ph/0307182v1, PDF p. 3, Proposition 2.1: common rank-block representation and midpoint summands

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P12

namespace QAlgorithms.Papers.Independent.Intakethird100.P12

open scoped ComplexConjugate ComplexOrder

/-- Proposition 2.1, PDF pp.3–4: the source's 'positive definite' means PSD;
only K is strict. The SAME sigma,A precede all midpoint summands. -/
theorem common_rank_block {n k : ℕ} (rho : Matrix (Fin n) (Fin n) ℂ)
    (hpsd : rho.PosSemidef) (hrank : rho.rank = k) (hkn : k < n) :
    ∃ (p : Equiv.Perm (Fin n)) (A : Matrix (Fin k) (Fin (n-k)) ℂ)
      (K : Matrix (Fin k) (Fin k) ℂ),
      K.PosDef ∧ permuteMatrix p rho = rankBlockMatrix hkn.le K A ∧
      ∀ (rhoFirst rhoSecond : Matrix (Fin n) (Fin n) ℂ),
        rhoFirst.PosSemidef → rhoSecond.PosSemidef →
        rho = (1 / 2 : ℂ) • (rhoFirst + rhoSecond) →
        ∃ (KFirst KSecond : Matrix (Fin k) (Fin k) ℂ),
          KFirst.PosSemidef ∧ KSecond.PosSemidef ∧
          permuteMatrix p rhoFirst = rankBlockMatrix hkn.le KFirst A ∧
          permuteMatrix p rhoSecond = rankBlockMatrix hkn.le KSecond A := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P12
