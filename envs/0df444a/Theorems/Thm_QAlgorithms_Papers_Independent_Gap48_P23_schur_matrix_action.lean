-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_schur_matrix_action
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.schur_matrix_action
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T22:55:32.631847+00:00
-- url     : https://prove2.me/theorems/eb5e9355-deda-4c35-9d4b-92fceaf52ae9
-- title:
--   Lemma B.9.
-- statement:
--   For $n\ge1$, write $\lambda=(n-k,k)$, $0\le k\le\lfloor n/2\rfloor$, $\ell_\lambda=n-2k$, $m_\lambda=\ell_\lambda+1$ and $d_\lambda=\binom nk-\binom n{k-1}$, where $\binom n{-1}=0$. The source vectors $|\lambda,w,i\rangle$ are constructed from the Dicke vector $|s_{\ell_\lambda}(w)\rangle$ followed by $k$ ordered normalized singlets. The same fixed real permutation coefficients are used for every $w$, and are orthonormalized and spanning only at $w=0$. All labels have their actual dependent ranges. Let $Q_\lambda(M)=\det(M)^kT^{n-2k}(M)$, where $T^\ell$ is the explicit normalized-monomial matrix of (C.9). Let $\Gamma$ be the source Schur transform followed by shape measurement and multiplicity trace, and let $\Gamma'$ append $I_{d_\lambda}/d_\lambda$ in each measured sector and apply inverse Schur. Write $\Theta$ for permutation averaging.
--
--   For every complex $2\times2$ matrix $M$,
--   $$M^{\otimes n}|\mu,v,j\rangle=\sum_{w=0}^{m_\mu-1}Q_\mu(M)_{wv}|\mu,w,j\rangle,$$
--   and $\langle\lambda,w,i|M^{\otimes n}|\mu,v,j\rangle=\delta_{\lambda\mu}\delta_{ij}Q_\mu(M)_{wv}$. The displayed upper endpoint corrects the source's extra undefined summand.
--
--   This identifies the source-constructed Schur coordinates and their operational use in the majority algorithm.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 56, Lemma B.9.

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

/-- PDF pp.56-57, Lemma B.9. PRINTED sum ends at m_mu inclusive; CHANGED to
Fin m_mu, because no ket with coordinate m_mu is defined. Both the vector
expansion and matrix-element identities are retained. Independent moderation required. -/
theorem schur_matrix_action (n : ℕ) (hn : 1 ≤ n)
    (alpha : RealSchurCoefficients n) (ha : LawfulCoefficients alpha) (M : Op (Fin 2)) :
    (∀ b : SchurIndex n, WithLp.toLp 2 ((tensorPower n M).mulVec (schurVector alpha b)) =
      ∑ w : Fin (degree n b.1 + 1), partitionIrrep n b.1 M w b.2.1 • schurVector alpha ⟨b.1, (w, b.2.2)⟩) ∧
    (∀ a b : SchurIndex n, inner ℂ (schurVector alpha a)
      (WithLp.toLp 2 ((tensorPower n M).mulVec (schurVector alpha b))) =
      if h : a.1 = b.1 then
        if a.2.2.val = b.2.2.val then partitionIrrep n a.1 M a.2.1 (h.symm ▸ b.2.1) else 0
      else 0) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
