-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_schur_permutation_blocks
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.schur_permutation_blocks
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:49:04.345146+00:00
-- url     : https://prove2.me/theorems/b331ed9d-58ac-41f8-9fe0-4378d1043cc8
-- title:
--   Lemma B.1.
-- statement:
--   For $n\ge1$, write $\lambda=(n-k,k)$, $0\le k\le\lfloor n/2\rfloor$, $\ell_\lambda=n-2k$, $m_\lambda=\ell_\lambda+1$ and $d_\lambda=\binom nk-\binom n{k-1}$, where $\binom n{-1}=0$. The source vectors $|\lambda,w,i\rangle$ are constructed from the Dicke vector $|s_{\ell_\lambda}(w)\rangle$ followed by $k$ ordered normalized singlets. The same fixed real permutation coefficients are used for every $w$, and are orthonormalized and spanning only at $w=0$. All labels have their actual dependent ranges. Let $Q_\lambda(M)=\det(M)^kT^{n-2k}(M)$, where $T^\ell$ is the explicit normalized-monomial matrix of (C.9). Let $\Gamma$ be the source Schur transform followed by shape measurement and multiplicity trace, and let $\Gamma'$ append $I_{d_\lambda}/d_\lambda$ in each measured sector and apply inverse Schur. Write $\Theta$ for permutation averaging.
--
--   For every permutation $\pi$ and valid labels,
--   $$\langle\lambda,w,i|P(\pi)|\mu,v,j\rangle=\delta_{\lambda\mu}\delta_{wv}\,P_\lambda(\pi)_{ij}.$$
--   The permutation block is computed at weight zero and is independent of $w,v$. Indices $i,j$ belong to their respective multiplicity spaces.
--
--   This identifies the source-constructed Schur coordinates and their operational use in the majority algorithm.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 49, Lemma B.1.

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

/-- PDF p.49, Lemma B.1: heterogeneous labels are compared by cases,
not ill-typed delta factors; the block is independent of both weights.
PRINTED: i,j both belong to [d_lambda]. CHANGED: each index belongs to its own
shape's schurMultiplicity range. WHY: otherwise the heterogeneous matrix element is
ill-typed. Independent moderation of this source correction is required. -/
theorem schur_permutation_blocks (n : ℕ) (hn : 1 ≤ n)
    (alpha : RealSchurCoefficients n) (ha : LawfulCoefficients alpha)
    (p : Equiv.Perm (Fin n)) (a b : SchurIndex n) :
    inner ℂ (schurVector alpha a)
      (WithLp.toLp 2 ((wordPermutationMatrix n 2 p).mulVec (schurVector alpha b))) =
      if h : a.1 = b.1 then
        if a.2.1.val = b.2.1.val then permutationBlock alpha a.1 p a.2.2 (h.symm ▸ b.2.2) else 0
      else 0 := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
