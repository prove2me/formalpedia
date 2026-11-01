-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P68_singularSchurComplement
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P68.singularSchurComplement
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:35:19.675977+00:00
-- url     : https://prove2.me/theorems/8cc969f2-7d40-48b4-bc02-544fe36c5548
-- title:
--   Singular Schur-complement positivity with both kernel conditions
-- statement:
--   Let $A\in\mathbb R^{n\times n}$ and $B\in\mathbb R^{m\times m}$ be symmetric positive-semidefinite matrices, and let $C\in\mathbb R^{n\times m}$ be arbitrary. Here $n,m$ count matrix coordinates, not bosonic modes. Put $M=\begin{pmatrix}A&C\\C^T&B\end{pmatrix}$. The following are equivalent:
--
--   $$
--   M\succeq0
--   \quad\Longleftrightarrow\quad
--   \bigl(\ker B\subseteq\ker C\ \text{ and }\ A-CB^+C^T\succeq0\bigr)
--   \quad\Longleftrightarrow\quad
--   \bigl(\ker A\subseteq\ker C^T\ \text{ and }\ B-C^TA^+C\succeq0\bigr).
--   $$
--
--   The inverses are spectral Moore–Penrose inverses, including zero eigenvalues. The kernel conditions are essential in the singular case. Lean records the two equivalences with $M\succeq0$ as their common left-hand side.
-- source:
--   Separability Criterion for all bipartite Gaussian States, arXiv:quant-ph/0104050v1, PDF p. 4, Appendix Lemma 1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P68

noncomputable section

open MeasureTheory Filter

open scoped BigOperators Topology ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakenext100.P68

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsSeparable IsBarycenter productCoeff)

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex)

open QAlgorithms.Papers.Independent.Claimed50.P19 (Cov)

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

/-- PDF p.4, Appendix Lemma 1: both singular Schur-complement equivalences.
Here n,m count matrix coordinates, not oscillator modes. Both kernel clauses
are retained, with no invertibility or positive-mode-count restriction. -/
theorem singularSchurComplement {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin m) (Fin m) ℝ)
    (C : Matrix (Fin n) (Fin m) ℝ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    ((Matrix.fromBlocks A C C.transpose B).PosSemidef ↔
      (∀ v : Fin m → ℝ, B.mulVec v = 0 → C.mulVec v = 0) ∧
      (A - C * hermitianInverse B * C.transpose).PosSemidef) ∧
    ((Matrix.fromBlocks A C C.transpose B).PosSemidef ↔
      (∀ v : Fin n → ℝ, A.mulVec v = 0 → C.transpose.mulVec v = 0) ∧
      (B - C.transpose * hermitianInverse A * C).PosSemidef) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P68

end
