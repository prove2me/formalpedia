-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P41_symplectic_spectral_symmetries
-- name    : QAlgorithms.Papers.Independent.Claimed50.P41.symplectic_spectral_symmetries
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:58:51.128977+00:00
-- url     : https://prove2.me/theorems/36f46657-2cc5-49a0-9db6-19a6bf10181c
-- title:
--   §IV (4.1)(v): spectral symmetries
-- statement:
--   Let $n\ge1$, let $\beta=\begin{pmatrix}0&I_n\\-I_n&0\end{pmatrix}$, and use grouped $(q_1,\ldots,q_n,p_1,\ldots,p_n)$ coordinates. Write $\mathrm{Sp}$ for the real matrices satisfying $S\beta S^T=\beta$, $K=\mathrm{Sp}\cap O(2n)$, and $\Pi$ for the symmetric positive definite matrices in $\mathrm{Sp}$. For $S\in\mathrm{Sp}$, let $m_S(z)$ denote the algebraic multiplicity of z as a root of its complex characteristic polynomial.
--
--   $$
--   0\notin\operatorname{spec}S,\quad m_S(z)=m_S(\overline z)=m_S(1/\overline z)\ (z\ne0),\quad m_S(1),m_S(-1)\in2\mathbb N.
--   $$
--
--   The two reflections preserve the complete eigenvalue multiset. Eigenspace dimensions are not used.
-- source:
--   The Real Symplectic Groups in Quantum Mechanics and Optics, arXiv:quant-ph/9509002v3, PDF p. 11, §IV (4.1)(v): spectral symmetries

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41

noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace QAlgorithms.Papers.Independent.Claimed50.P41

/-- PDF p.11, (4.1)(v): spectral symmetries count algebraic multiplicity.
Reflection through the unit circle sends lambda to inverse(conjugate lambda). -/
theorem symplectic_spectral_symmetries (n : ℕ) (hn : 0 < n)
    (S : Matrix (Phase n) (Phase n) ℝ) (hS : PreservesCanonicalForm S) :
    let p := (complexify S).charpoly
    ¬ p.IsRoot 0 ∧
    (∀ z : ℂ, Polynomial.rootMultiplicity z p = Polynomial.rootMultiplicity (star z) p) ∧
    (∀ z : ℂ, z ≠ 0 → Polynomial.rootMultiplicity z p =
      Polynomial.rootMultiplicity ((star z)⁻¹) p) ∧
    Even (Polynomial.rootMultiplicity (1 : ℂ) p) ∧
    Even (Polynomial.rootMultiplicity (-1 : ℂ) p) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P41

end
