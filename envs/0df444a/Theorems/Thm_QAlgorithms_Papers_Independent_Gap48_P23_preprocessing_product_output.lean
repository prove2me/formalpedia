-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_preprocessing_product_output
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.preprocessing_product_output
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:34:16.958979+00:00
-- url     : https://prove2.me/theorems/24b8bead-c4a2-492e-8f0a-2cca4d1541ef
-- title:
--   Lemma 3.2.
-- statement:
--   For $n\ge1$, write $\lambda=(n-k,k)$, $0\le k\le\lfloor n/2\rfloor$, $\ell_\lambda=n-2k$, $m_\lambda=\ell_\lambda+1$ and $d_\lambda=\binom nk-\binom n{k-1}$, where $\binom n{-1}=0$. The source vectors $|\lambda,w,i\rangle$ are constructed from the Dicke vector $|s_{\ell_\lambda}(w)\rangle$ followed by $k$ ordered normalized singlets. The same fixed real permutation coefficients are used for every $w$, and are orthonormalized and spanning only at $w=0$. All labels have their actual dependent ranges. Let $Q_\lambda(M)=\det(M)^kT^{n-2k}(M)$, where $T^\ell$ is the explicit normalized-monomial matrix of (C.9). Let $\Gamma$ be the source Schur transform followed by shape measurement and multiplicity trace, and let $\Gamma'$ append $I_{d_\lambda}/d_\lambda$ in each measured sector and apply inverse Schur. Write $\Theta$ for permutation averaging.
--
--   For every $x,U$, with $h=|x|$, the outcome probability and unnormalized retained sector are
--   $$p_k(h)=\begin{cases}\dfrac{\binom nk-\binom n{k-1}}{\binom nh},&k\le h\le n-k,\\0,&\text{otherwise},\end{cases}\qquad\Gamma_\lambda(\rho_x^U)=p_k(h)Q_\lambda(U)|h-k\rangle\langle h-k|Q_\lambda(U)^\dagger.$$
--   The trace of the displayed block is $p_k(h)$. The branch ket is formed only on its valid support. The added upper support bound corrects the printed omission.
--
--   This identifies the source-constructed Schur coordinates and their operational use in the majority algorithm.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 22, Lemma 3.2.

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P23

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P23

open MeasureTheory

open scoped ComplexConjugate Matrix ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Exact frozen coordinate helpers; no paper-local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

/-- PDF p.22, Lemma 3.2, with the support correction documented above.
Each unnormalized block gives both the outcome probability and its pure
conditional state on nonzero-probability sectors. -/
theorem preprocessing_product_output (n : ℕ) (hn : 1 ≤ n)
    (alpha : RealSchurCoefficients n) (ha : LawfulCoefficients alpha)
    (x : Word n 2) (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    ∀ k : TwoRowShape n,
      (preprocessingBranch alpha k (encodedInput U.val x)).trace = samplingProbability n (booleanWordWeight x) k ∧
      preprocessingBranch alpha k (encodedInput U.val x) = predictedBranch n k (booleanWordWeight x) U.val := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
