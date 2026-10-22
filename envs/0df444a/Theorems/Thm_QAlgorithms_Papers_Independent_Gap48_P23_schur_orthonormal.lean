-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_schur_orthonormal
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.schur_orthonormal
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:54:02.439703+00:00
-- url     : https://prove2.me/theorems/94a48eae-40e6-4be6-9b77-6c97c8fdc4a7
-- title:
--   Lemma B.7.
-- statement:
--   For $n\ge1$, write $\lambda=(n-k,k)$, $0\le k\le\lfloor n/2\rfloor$, $\ell_\lambda=n-2k$, $m_\lambda=\ell_\lambda+1$ and $d_\lambda=\binom nk-\binom n{k-1}$, where $\binom n{-1}=0$. The source vectors $|\lambda,w,i\rangle$ are constructed from the Dicke vector $|s_{\ell_\lambda}(w)\rangle$ followed by $k$ ordered normalized singlets. The same fixed real permutation coefficients are used for every $w$, and are orthonormalized and spanning only at $w=0$. All labels have their actual dependent ranges. Let $Q_\lambda(M)=\det(M)^kT^{n-2k}(M)$, where $T^\ell$ is the explicit normalized-monomial matrix of (C.9). Let $\Gamma$ be the source Schur transform followed by shape measurement and multiplicity trace, and let $\Gamma'$ append $I_{d_\lambda}/d_\lambda$ in each measured sector and apply inverse Schur. Write $\Theta$ for permutation averaging.
--
--   For every positive $n$ and all valid labels,
--   $$\langle\lambda,w,i|\mu,v,j\rangle=\delta_{\lambda\mu}\delta_{wv}\delta_{ij}.$$
--   The heterogeneous delta is represented by equality of dependent total labels.
--
--   This identifies the source-constructed Schur coordinates and their operational use in the majority algorithm.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 55, Lemma B.7.

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

/-- PDF p.55, Lemma B.7: complete heterogeneous inner-product identity. -/
theorem schur_orthonormal (n : ℕ) (hn : 1 ≤ n)
    (alpha : RealSchurCoefficients n) (ha : LawfulCoefficients alpha) (a b : SchurIndex n) :
    inner ℂ (schurVector alpha a) (schurVector alpha b) = if a = b then 1 else 0 := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
