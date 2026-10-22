-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_preprocessing_symmetries
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.preprocessing_symmetries
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:33:17.54999+00:00
-- url     : https://prove2.me/theorems/e139c506-8fa6-4ec9-9741-1780ba04f428
-- title:
--   Lemma 3.1.
-- statement:
--   For $n\ge1$, write $\lambda=(n-k,k)$, $0\le k\le\lfloor n/2\rfloor$, $\ell_\lambda=n-2k$, $m_\lambda=\ell_\lambda+1$ and $d_\lambda=\binom nk-\binom n{k-1}$, where $\binom n{-1}=0$. The source vectors $|\lambda,w,i\rangle$ are constructed from the Dicke vector $|s_{\ell_\lambda}(w)\rangle$ followed by $k$ ordered normalized singlets. The same fixed real permutation coefficients are used for every $w$, and are orthonormalized and spanning only at $w=0$. All labels have their actual dependent ranges. Let $Q_\lambda(M)=\det(M)^kT^{n-2k}(M)$, where $T^\ell$ is the explicit normalized-monomial matrix of (C.9). Let $\Gamma$ be the source Schur transform followed by shape measurement and multiplicity trace, and let $\Gamma'$ append $I_{d_\lambda}/d_\lambda$ in each measured sector and apply inverse Schur. Write $\Theta$ for permutation averaging.
--
--   The constructed preprocessing is a channel and, for every operator $X$, permutation $\pi$, and $U\in U(2)$,
--   $$\Gamma(P(\pi)XP(\pi)^\dagger)=\Gamma(X),\quad\Gamma(U^{\otimes n}XU^{\dagger\otimes n})=Q(U)\Gamma(X)Q(U)^\dagger,$$
--   where $Q(U)=\bigoplus_\lambda Q_\lambda(U)$.
--
--   This identifies the source-constructed Schur coordinates and their operational use in the majority algorithm.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 21, Lemma 3.1.

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

/-- PDF p.21, Lemma 3.1: channel legality, permutation invariance and covariance. -/
theorem preprocessing_symmetries (n : ℕ) (hn : 1 ≤ n)
    (alpha : RealSchurCoefficients n) (ha : LawfulCoefficients alpha) :
    IsChannel (preprocessing alpha) ∧
    (∀ p rho, preprocessing alpha (conjSuperop (wordPermutationMatrix n 2 p) rho) = preprocessing alpha rho) ∧
    (∀ (U : Matrix.unitaryGroup (Fin 2) ℂ) rho,
      preprocessing alpha (conjSuperop (tensorPower n U.val) rho) =
        conjSuperop (reducedAction n U.val) (preprocessing alpha rho)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
