-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P41_variance_family_dimensions
-- name    : QAlgorithms.Papers.Independent.Claimed50.P41.variance_family_dimensions
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:08:50.995161+00:00
-- url     : https://prove2.me/theorems/1981a66c-67e0-47b6-8f7e-2fcda77f6265
-- title:
--   §XI: dimensions of the four variance families
-- statement:
--   Let $n\ge1$, let $\beta=\begin{pmatrix}0&I_n\\-I_n&0\end{pmatrix}$, and use grouped $(q_1,\ldots,q_n,p_1,\ldots,p_n)$ coordinates. For a real symmetric covariance matrix $V$, put $V^{(c)}=\Omega V\Omega^\dagger=\begin{pmatrix}A&B\\\overline B&\overline A\end{pmatrix}$, where $\Omega=2^{-1/2}\begin{pmatrix}I&iI\\I&-iI\end{pmatrix}$. Let $\mathcal S=\{V>0:V+i\beta/2\succeq0\}$. Vacuum has covariance $I/2$. Let SK consist of V in S with AB symmetric, SH of members of SK with B=0 and A-I/2 positive semidefinite, and SG of members of SK with 2V positive symplectic.
--
--   $$
--   \dim\mathcal S=n(2n+1),\quad\dim\mathcal S_K=n(n+2),\quad\dim\mathcal S_H=n^2,\quad\dim\mathcal S_G=n(n+1).
--   $$
--
--   Dimension here is global Hausdorff dimension in the ambient finite-dimensional real matrix space, the pinned interpretation of the source parameter-family counts. It does not assume smoothness at boundaries or repeated spectra.
-- source:
--   The Real Symplectic Groups in Quantum Mechanics and Optics, arXiv:quant-ph/9509002v3, PDF p. 34, §XI: dimensions of the four variance families

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41

noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace QAlgorithms.Papers.Independent.Claimed50.P41

/-- PDF pp.33–34: global real parameter dimensions of S, SK, SH, SG.
Hausdorff dimension in the finite real matrix space includes boundary and
repeated-spectrum strata without assuming these sets are manifolds. -/
theorem variance_family_dimensions (n : ℕ) (hn : 0 < n) :
    dimH {V : Matrix (Phase n) (Phase n) ℝ | Allowed V} = (n * (2 * n + 1) : ℕ) ∧
    dimH (familyK n) = (n * (n + 2) : ℕ) ∧
    dimH (familyH n) = (n ^ 2 : ℕ) ∧
    dimH (familyG n) = (n * (n + 1) : ℕ) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P41

end
