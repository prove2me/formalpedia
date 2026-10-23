-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P41_complex_canonical_coordinates
-- name    : QAlgorithms.Papers.Independent.Claimed50.P41.complex_canonical_coordinates
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T10:59:57.335258+00:00
-- url     : https://prove2.me/theorems/54ed5bbd-6373-42f5-bc50-1459e04f5efc
-- title:
--   §IV (4.3)–(4.6): complex canonical coordinates
-- statement:
--   Let $n\ge1$, let $\beta=\begin{pmatrix}0&I_n\\-I_n&0\end{pmatrix}$, and use grouped $(q_1,\ldots,q_n,p_1,\ldots,p_n)$ coordinates. Let $H=L^2(\mathbb R^n,dq;\mathbb C)$, with $\hbar=1$, and $D(d,p)f(q)=e^{ip\cdot(q-d/2)}f(q-d)$. An implementer of $S$ is a surjective complex-linear Hilbert isometry satisfying $UD(z)=D(Sz)U$; equalities of wavefunctions mean almost-everywhere equalities. On the common Schwartz core put $a_r=(q_r+ip_r)/\sqrt2$ and $a_r^\dagger=(q_r-ip_r)/\sqrt2$, and use $\Omega=2^{-1/2}\begin{pmatrix}I&iI\\I&-iI\end{pmatrix}$ for complex coordinates.
--
--   $$
--   \Omega^\dagger\Omega=I,\quad [a_r,a_s^\dagger]=\delta_{rs}I,\quad[a_r,a_s]=[a_r^\dagger,a_s^\dagger]=0,\quad S^{(c)}=\Omega S\Omega^\dagger.
--   $$
--
--   The statement gives both full CCR matrices, beta and Sigma3, and all four complex blocks in (4.6), namely the top blocks (A+D+i(C-B))/2 and (A-D+i(B+C))/2 and their entrywise conjugates. Differential expressions are applied on Schwartz functions.
-- source:
--   The Real Symplectic Groups in Quantum Mechanics and Optics, arXiv:quant-ph/9509002v3, PDF p. 12, §IV (4.3)–(4.6): complex canonical coordinates

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41

noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace QAlgorithms.Papers.Independent.Claimed50.P41

/-- PDF pp.11–12, (4.3)–(4.6): actual ladder CCR on the common Schwartz
core and the exact unitary coordinate change and block transformation. -/
theorem complex_canonical_coordinates (n : ℕ) (hn : 0 < n)
    (A B C D : Matrix (Fin n) (Fin n) ℝ) :
    (canonicalCoordinateMatrix n).conjTranspose * canonicalCoordinateMatrix n = 1 ∧ canonicalCoordinateMatrix n * (canonicalCoordinateMatrix n).conjTranspose = 1 ∧
    canonicalCoordinateMatrix n * (Complex.I • complexify (sigma n)) * (canonicalCoordinateMatrix n).transpose = complexify (sigma n) ∧
    canonicalCoordinateMatrix n * (Complex.I • complexify (sigma n)) * (canonicalCoordinateMatrix n).conjTranspose = sigma3 n ∧
    complexForm (Matrix.fromBlocks A B C D) = (1 / 2 : ℂ) • Matrix.fromBlocks
      (complexify (A + D) + Complex.I • complexify (C - B))
      (complexify (A - D) + Complex.I • complexify (B + C))
      (complexify (A - D) - Complex.I • complexify (B + C))
      (complexify (A + D) + Complex.I • complexify (B - C)) ∧
    (∀ (f : SchwartzMap (Fin n → ℝ) ℂ) (r s : Fin n) (q : Fin n → ℝ),
      annihilationFunction r (creationFunction s f) q -
        creationFunction s (annihilationFunction r f) q = kronecker r s * f q ∧
      annihilationFunction r (annihilationFunction s f) q -
        annihilationFunction s (annihilationFunction r f) q = 0 ∧
      creationFunction r (creationFunction s f) q -
        creationFunction s (creationFunction r f) q = 0) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P41

end
