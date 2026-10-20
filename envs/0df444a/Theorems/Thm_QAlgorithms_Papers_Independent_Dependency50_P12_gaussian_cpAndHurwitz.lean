-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P12_gaussian_cpAndHurwitz
-- name    : QAlgorithms.Papers.Independent.Dependency50.P12.gaussian_cpAndHurwitz
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:04:52.985454+00:00
-- url     : https://prove2.me/theorems/21d9ff2d-dc93-4640-a17b-09a07f039465
-- title:
--   §6.3: Gaussian complete positivity versus Hurwitz threshold
-- statement:
--   Use only the finite Gaussian moment representation, with quadrature order \((Q,P)\), \([Q,P]=i\), \(r\in\mathbb R\), and \(\gamma\ge0\). Set
--   \[
--   A=\operatorname{diag}(-\gamma/2-r,-\gamma/2+r),\quad
--   D=(\gamma/2)I,\quad
--   \Omega=\begin{pmatrix}0&1\\-1&0\end{pmatrix}.
--   \]
--   The infinitesimal CP matrix \(D-\frac i2(A\Omega+\Omega A^T)\) has eigenvalues \(0,\gamma\), so its positivity criterion is \(\gamma\ge0\), independent of \(r\). The drift eigenvalues are \(-\gamma/2\pm|r|\), and
--   \[
--   A\text{ is Hurwitz}\iff\gamma>2|r|.
--   \]
--   Independent positive rescaling of the squeezing and damping rays preserves their Lie algebra and minimal local wedge. The selected sum can change stability across the strict threshold. No infinite-dimensional QDS is constructed.
-- source:
--   The Geometry of Dissipative Complexity: A Levi-Type Decomposition Theorem for Markovian Quantum Dynamics via Lie Wedges and Invariant Cones, arXiv:2608.27330v1, PDF p. 38, §6.3: Gaussian complete positivity versus Hurwitz threshold

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P12

noncomputable section

open scoped Matrix ComplexOrder Matrix.Norms.Frobenius

open Set

namespace QAlgorithms.Papers.Independent.Dependency50.P12

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] Classical.propDecidable Classical.decEq

open Coordinates

open QAlgorithms.Papers.Independent.Information100

attribute [local instance] QAlgorithms.Papers.Independent.Dependency50.P12.inheritedSubalgebraTopologicalAddGroup

/-- arXiv:2608.27330v1, PDF pp.38--39, Section 6.3 spectral/CP assertion.
No infinite-dimensional oscillator semigroup is asserted. Spectra are recorded
with multiplicity by characteristic polynomials; the threshold is strict. -/
theorem gaussian_cpAndHurwitz (r gamma : ℝ) (hg : 0 ≤ gamma) :
    (gaussianCP r gamma).charpoly = Polynomial.X * (Polynomial.X - Polynomial.C (gamma : ℂ)) ∧
    ((gaussianCP r gamma).PosSemidef ↔ 0 ≤ gamma) ∧
    (gaussianA r gamma).charpoly =
      (Polynomial.X - Polynomial.C (-gamma/2 + |r|)) *
      (Polynomial.X - Polynomial.C (-gamma/2 - |r|)) ∧
    (Hurwitz (gaussianA r gamma) ↔ 2 * |r| < gamma) ∧
    (∀ a b : ℝ, 0 < a → 0 < b →
      LieSubalgebra.lieSpan ℝ (Matrix (Fin 6) (Fin 6) ℝ) (gaussianG (a*r) (b*gamma)) =
        LieSubalgebra.lieSpan ℝ (Matrix (Fin 6) (Fin 6) ℝ) (gaussianG r gamma) ∧
      minimalWedge (gaussianG (a*r) (b*gamma)) = minimalWedge (gaussianG r gamma)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P12

end
