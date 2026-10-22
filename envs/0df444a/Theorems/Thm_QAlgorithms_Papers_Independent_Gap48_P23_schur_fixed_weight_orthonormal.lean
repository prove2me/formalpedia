-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_schur_fixed_weight_orthonormal
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.schur_fixed_weight_orthonormal
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:53:23.761333+00:00
-- url     : https://prove2.me/theorems/e7a0d223-e4d5-4a79-afeb-3af78d0ad3a7
-- title:
--   Proposition B.6.
-- statement:
--   For $n\ge1$, write $\lambda=(n-k,k)$, $0\le k\le\lfloor n/2\rfloor$, $\ell_\lambda=n-2k$, $m_\lambda=\ell_\lambda+1$ and $d_\lambda=\binom nk-\binom n{k-1}$, where $\binom n{-1}=0$. The source vectors $|\lambda,w,i\rangle$ are constructed from the Dicke vector $|s_{\ell_\lambda}(w)\rangle$ followed by $k$ ordered normalized singlets. The same fixed real permutation coefficients are used for every $w$, and are orthonormalized and spanning only at $w=0$. All labels have their actual dependent ranges. Let $Q_\lambda(M)=\det(M)^kT^{n-2k}(M)$, where $T^\ell$ is the explicit normalized-monomial matrix of (C.9). Let $\Gamma$ be the source Schur transform followed by shape measurement and multiplicity trace, and let $\Gamma'$ append $I_{d_\lambda}/d_\lambda$ in each measured sector and apply inverse Schur. Write $\Theta$ for permutation averaging.
--
--   For each shape and valid weight, weight-zero orthonormalization implies
--   $$\langle\lambda,w,i|\lambda,w,j\rangle=\delta_{ij}.$$
--   No orthonormality assumption at nonzero weight is made.
--
--   This identifies the source-constructed Schur coordinates and their operational use in the majority algorithm.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 55, Proposition B.6.

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

/-- PDF p.55, Proposition B.6: booleanWordWeight-zero orthonormalization propagates to every w. -/
theorem schur_fixed_weight_orthonormal (n : ℕ) (hn : 1 ≤ n)
    (alpha : RealSchurCoefficients n) (ha : LawfulCoefficients alpha) (k : TwoRowShape n)
    (w : Fin (degree n k + 1)) (i j : Fin (schurMultiplicity n k)) :
    inner ℂ (schurVector alpha ⟨k, (w, i)⟩) (schurVector alpha ⟨k, (w, j)⟩) =
      if i = j then 1 else 0 := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
