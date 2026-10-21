-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P39_square_root_measurement
-- name    : QAlgorithms.Papers.Independent.Next46.P39.square_root_measurement
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:46:14.601687+00:00
-- url     : https://prove2.me/theorems/c2808d8b-ec32-47b1-8de9-5dfe0e8174a9
-- title:
--   The optimal compressed measurement is a square-root measurement
-- statement:
--   For normalized Schmidt input $\Psi$ in the compact finite-dimensional model, let $F=\int_G U_g|\Psi\rangle\langle\Psi|U_g^\dagger\,dg$ be its frame operator and let $F^{-1/2}$ invert positive square-root eigenvalues and vanish on the kernel. Then
--
--   $$F=\bigoplus_\mu\frac{|c_\mu|^2}{d_\mu}I_{d_\mu}\otimes\sum_t\lambda_{\mu t}|\phi_{\mu t}\rangle\langle\phi_{\mu t}|,\qquad F^{-1/2}\Psi=\eta.$$
--
--   There exists a normalized covariant seed whose compression to the cyclic orbit subspace is $|\eta\rangle\langle\eta|$ and whose likelihood attains the explicit optimum of Theorem 1. This identifies the square-root measurement on its actual support without imposing invertibility on the entire Hilbert space.
-- source:
--   Maximum likelihood estimation for a group of physical transformations, arXiv:quant-ph/0507007v1, PDF p. 8, §2.5 Remark II: maximum-likelihood measurement is the square-root measurement

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P39

open MeasureTheory

open scoped ComplexConjugate Matrix ComplexOrder Matrix.Norms.L2Operator Manifold ContDiff

open QAlgorithms.Measurements (DensityPOVM)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

attribute [local instance] Classical.propDecidable

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P39.operatorMatrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P39.operatorMatrixBorel

variable {G I S : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype S] [DecidableEq S] [Nonempty S]

variable (R : FiniteModel G I S)

variable {R}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [ChartedSpace E G]

/-- PDF p.8, Remark II: Haar frame, its explicit block form, and the
square-root vector, with existence of a normalized full-space completion. -/
theorem square_root_measurement (_finite : FiniteDimensional ℝ E) (_lie : LieGroup 𝓘(ℝ, E) ∞ G)
    (R : FiniteModel G I S) (D : SchmidtInput R) :
    frame (R := R) D.vector =
      ∑ s, R.embed s * Matrix.kronecker
        (((Complex.normSq (D.c s) / R.d s : ℝ) : ℂ) •
          (1 : Matrix (Fin (R.d s)) (Fin (R.d s)) ℂ))
        (∑ t, (D.lam s t : ℂ) • QAlgorithms.pureDensity (D.right s t)) * (R.embed s)ᴴ ∧
    QAlgorithms.act (inverseSqrt (frame (R := R) D.vector)) D.vector = D.eta ∧
    (∃ Xi, IsSeed R Xi ∧
      D.projector * Xi * D.projector = QAlgorithms.pureDensity D.eta ∧
      likelihood Xi (QAlgorithms.pureDensity D.vector) = D.formula) := by sorry

end QAlgorithms.Papers.Independent.Next46.P39

end
