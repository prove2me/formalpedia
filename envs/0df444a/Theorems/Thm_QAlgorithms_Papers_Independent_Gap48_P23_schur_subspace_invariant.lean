-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_schur_subspace_invariant
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.schur_subspace_invariant
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:54:46.935268+00:00
-- url     : https://prove2.me/theorems/e1f88f7c-0525-4e49-a6f5-f0786766a944
-- title:
--   Lemma B.8.
-- statement:
--   For $n\ge1$, write $\lambda=(n-k,k)$, $0\le k\le\lfloor n/2\rfloor$, $\ell_\lambda=n-2k$, $m_\lambda=\ell_\lambda+1$ and $d_\lambda=\binom nk-\binom n{k-1}$, where $\binom n{-1}=0$. The source vectors $|\lambda,w,i\rangle$ are constructed from the Dicke vector $|s_{\ell_\lambda}(w)\rangle$ followed by $k$ ordered normalized singlets. The same fixed real permutation coefficients are used for every $w$, and are orthonormalized and spanning only at $w=0$. All labels have their actual dependent ranges. Let $Q_\lambda(M)=\det(M)^kT^{n-2k}(M)$, where $T^\ell$ is the explicit normalized-monomial matrix of (C.9). Let $\Gamma$ be the source Schur transform followed by shape measurement and multiplicity trace, and let $\Gamma'$ append $I_{d_\lambda}/d_\lambda$ in each measured sector and apply inverse Schur. Write $\Theta$ for permutation averaging.
--
--   For every $n\ge1$, shape $\lambda$, multiplicity label $i$ and complex $2\times2$ matrix $M$,
--   $$M^{\otimes n}\mathcal Q_{\lambda,i}\subseteq\mathcal Q_{\lambda,i},\qquad\mathcal Q_{\lambda,i}=\operatorname{span}\{|\lambda,w,i\rangle:w\in[m_\lambda]\}.$$
--   The matrix need not be unitary or invertible.
--
--   This identifies the source-constructed Schur coordinates and their operational use in the majority algorithm.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 56, Lemma B.8.

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

/-- PDF p.56, Lemma B.8: invariant under every complex 2x2 matrix, including singular ones. -/
theorem schur_subspace_invariant (n : ℕ) (hn : 1 ≤ n)
    (alpha : RealSchurCoefficients n) (ha : LawfulCoefficients alpha) (k : TwoRowShape n)
    (i : Fin (schurMultiplicity n k)) (M : Op (Fin 2)) :
    ∀ v ∈ unitarySubspace alpha k i,
      WithLp.toLp 2 ((tensorPower n M).mulVec v) ∈ unitarySubspace alpha k i := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
