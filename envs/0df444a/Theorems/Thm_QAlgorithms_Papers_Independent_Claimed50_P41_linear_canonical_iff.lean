-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P41_linear_canonical_iff
-- name    : QAlgorithms.Papers.Independent.Claimed50.P41.linear_canonical_iff
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:54:35.163071+00:00
-- url     : https://prove2.me/theorems/890fa1ca-6a9b-441a-a73b-29800737cec6
-- title:
--   §II (2.3)–(2.6): linear canonical transformations
-- statement:
--   Let $n\ge1$, let $\beta=\begin{pmatrix}0&I_n\\-I_n&0\end{pmatrix}$, and use grouped $(q_1,\ldots,q_n,p_1,\ldots,p_n)$ coordinates. For a real matrix $S$, let $b_{ab}=\sum_{ij}S_{ai}\beta_{ij}S_{bj}$ denote the transformed Poisson-bracket coefficient, or equivalently the quantum commutator coefficient after division by $i\hbar$.
--
--   $$
--   (\forall a,b,\ b_{ab}=\beta_{ab})\ \Longleftrightarrow\ S\beta S^T=\beta.
--   $$
--
--   This also agrees with Mathlib symplectic-group membership despite its opposite sign for the defining form. The theorem concerns homogeneous linear changes; translations are a separate node.
-- source:
--   The Real Symplectic Groups in Quantum Mechanics and Optics, arXiv:quant-ph/9509002v3, PDF p. 6, §II (2.3)–(2.6): linear canonical transformations

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41

noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace QAlgorithms.Papers.Independent.Claimed50.P41

/-- PDF pp.5–6, (2.3)–(2.6): preservation of all canonical PB/CCR coefficients
is exactly S beta S^T=beta; membership in Mathlib uses the opposite-sign J. -/
theorem linear_canonical_iff (n : ℕ) (hn : 0 < n)
    (S : Matrix (Phase n) (Phase n) ℝ) :
    ((∀ a b, linearCanonicalBracket S a b = sigma n a b) ↔ PreservesCanonicalForm S) ∧
    (PreservesCanonicalForm S ↔ S ∈ Matrix.symplecticGroup (Fin n) ℝ) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P41

end
