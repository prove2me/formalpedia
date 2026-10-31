-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P39_real_sign_counts_and_total_signature
-- name    : QAlgorithms.Papers.Independent.Intake100.P39.real_sign_counts_and_total_signature
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:10:26.610838+00:00
-- url     : https://prove2.me/theorems/567e4988-c36c-47cd-afbb-617d654fca40
-- title:
--   Proposition 12 — real sign counts and total signature
-- statement:
--   Let $V=\mathbb R^{2n}$, with grouped symplectic form $\Omega(x,y)=\sum_{i=1}^n(x_i y_{n+i}-x_{n+i}y_i)$, and let $A$ be a real linear map preserving $\Omega$. This is a coordinate formulation in an arbitrary ambient symplectic basis. Write $A_{\mathbb C}$ and $\Omega_{\mathbb C}$ for their complex-linear and complex-bilinear extensions, $N_\lambda=A_{\mathbb C}-\lambda I$, and $E_\lambda=\bigcup_{r\ge1}\ker N_\lambda^r$. Let $[\lambda]=\{\lambda,\lambda^{-1},\bar\lambda,\bar\lambda^{-1}\}$, with repetitions removed, and let $V_{[\lambda]}$ be the real subspace whose complexification is $\sum_{\mu\in[\lambda]}E_\mu$. A symplectic basis uses the matrix $\left(\begin{smallmatrix}0&I\\-I&0\end{smallmatrix}\right)$. All transposes below are ordinary transposes.
--
--   For a positive integer $r$, let $J(\lambda,r)$ have diagonal $\lambda$, superdiagonal $1$, and other entries zero. Put $D(r,s)=\operatorname{diag}(0,\ldots,0,s)$ and
--   $$B(\lambda,r,s)=\begin{pmatrix}J(\lambda,r)^{-1}&J(\lambda,r)^{-1}D(r,s)\\0&J(\lambda,r)^T\end{pmatrix}.$$
--   The symbol $\diamond$ denotes the symplectic direct sum: concatenate all first-half basis vectors before all second-half basis vectors.
--   For $a\in\{1,-1\}$ and $k\ge1$, define the real symmetric kernel form on $\ker(A-aI)^{2k}$ by
--   $$Q^a_{2k}(v,w)=a\,\Omega((A-aI)^k v,(A-aI)^{k-1}w).$$
--   Its positive and negative indices count positive and negative eigenvalues, excluding zeros; its rank is their sum and its signature is their difference.
--   Consider any valid signed real normal decomposition $\diamond_j B(a,r_j,s_j)$ on $V_{[a]}$, $a=\pm1$. For every $k\ge1$,
--   $$n_+(Q^a_{2k})=\#\{j:r_j=k,s_j=1\},\qquad n_-(Q^a_{2k})=\#\{j:r_j=k,s_j=-1\}.$$
--   Moreover, with the source's ambient dimension bound,
--   $$\sum_j s_j=\sum_{k=1}^{\dim V}\operatorname{Signature}(Q^a_{2k}).$$
--   Here $n_+$ and $n_-$ denote the positive and negative indices. The forms may have zero eigenvalues.
--
--
--   This recovers both sign multiplicities and the finite total signature formula (22).
-- source:
--   Normal Forms for Symplectic Matrices, arXiv:1307.2403v2, PDF p. 17, Proposition 12 — real sign counts and total signature

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P39

noncomputable section

open scoped BigOperators Matrix

namespace QAlgorithms.Papers.Independent.Intake100.P39

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse only the pinned accepted substrate, with definitionally identical coordinate models.
-- The imported symplectic predicate preserves -Omega0, equivalent to preserving Omega0.

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

open QAlgorithms.Papers.Independent.Gap50repair.P01
  (Coord GroupedRealMatrix omegaMatrix omegaR omegaC shifted generalizedSpace
    IsEigenvalue HasNilpotentHeight restrictedKernel GeneralizedQuotient)

/-- PDF pp.17–18, Proposition 12: BOTH inertia counts and the finite total
signature identity (22), whose upper bound is the ambient dim V=2n. -/
theorem real_sign_counts_and_total_signature {n L : ℕ} (A : GroupedRealMatrix n)
    (hA : IsSymplectic A) (a : ℝ) (ha : a = 1 ∨ a = -1)
    (r : Fin L → ℕ) (s : Fin L → ℤ) (hNF : RealNormal A a r s) :
    RealSignCounts A a r s ∧
      (∑ j, s j) = ∑ k ∈ Finset.Icc 1 (2 * n), (rankSignature (realInertia A a k)).2 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P39

end
