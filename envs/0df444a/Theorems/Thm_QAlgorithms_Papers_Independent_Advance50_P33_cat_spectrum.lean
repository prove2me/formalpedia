-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P33_cat_spectrum
-- name    : QAlgorithms.Papers.Independent.Advance50.P33.cat_spectrum
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:35:15.090457+00:00
-- url     : https://prove2.me/theorems/09ced499-8deb-422c-a9a0-faca90a62a40
-- title:
--   Corrected cat-basis spectral decomposition of the token difference
-- statement:
--   Let $a\in\mathbb C\setminus\{0\}$, $H=\rho_0-\rho_1$ for the actual token reductions of Eq. (3), and
--   $$
--   |+\rangle=\frac{|a\rangle+|-a\rangle}{\sqrt{2(1+e^{-2|a|^2})}},\quad
--   |-\rangle=\frac{|a\rangle-|-a\rangle}{\sqrt{2(1-e^{-2|a|^2})}},\quad
--   t=\frac{e^{-2|a|^2}}{1+e^{-4|a|^2}}.
--   $$
--   These cats are orthonormal and the spectral decomposition and eigenvector identities are
--   $$
--   H=-t|+\rangle\langle+|+t|-\rangle\langle-|,\qquad
--   H|+\rangle=-t|+\rangle,\quad H|-\rangle=t|-\rangle.
--   $$
--   This identifies the full operator, including its zero action on the orthogonal complement of the cat span.
--
--   **Source correction.** Eq. (14) prints the opposite sign assignment. The statement preserves the source's $H=\rho_0-\rho_1$ and even/odd labels and corrects those eigenvalue signs. Eqs. (15)--(16), which depend only on their magnitudes, remain unchanged.
-- source:
--   Quantum bit commitment under Gaussian constraints, arXiv:1105.2140v2, PDF p. 7, IV, Eq.(14): cat-basis spectral decomposition, corrected sign labels

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P33

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P33

open Filter

open scoped BigOperators Topology

open QAlgorithms.Papers.Independent.Dependency50.P39
  (Fock FockOperator BipartiteFock fockKet bipartiteKet coherentKet
   coherentCoefficient CoherentRealized displacement displacementMatrix
   DisplacementRealized HasFockMatrix operatorOfMatrix IsDensity IsTraceClass
   nuclearTraceNorm fockTrace)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.7, Eq.(14), CORRECTED SIGN LABELS: the printed lambda_+=+t on even
and lambda_-=-t on odd are reversed. For H=rho_0-rho_1, even has -t and odd
has +t. The definitions of H and |+>,|-> are preserved; Eqs.(15)--(16) are
unchanged. The discrepancy is recorded in HARD.md for independent moderation. -/
theorem cat_spectrum (a : ℂ) (ha : a ≠ 0) :
    CoherentRealized ∧
    ‖cat a true‖ = 1 ∧ ‖cat a false‖ = 1 ∧ inner ℂ (cat a true) (cat a false) = 0 ∧
    tokenDifference a =
      (-tokenEigenvalue a : ℝ) • InnerProductSpace.rankOne ℂ (cat a true) (cat a true) +
        (tokenEigenvalue a : ℝ) • InnerProductSpace.rankOne ℂ (cat a false) (cat a false) ∧
    tokenDifference a (cat a true) = (-tokenEigenvalue a : ℂ) • cat a true ∧
    tokenDifference a (cat a false) = (tokenEigenvalue a : ℂ) • cat a false := by sorry

end QAlgorithms.Papers.Independent.Advance50.P33

end
