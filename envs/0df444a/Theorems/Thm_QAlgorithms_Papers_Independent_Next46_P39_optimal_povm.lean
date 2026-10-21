-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P39_optimal_povm
-- name    : QAlgorithms.Papers.Independent.Next46.P39.optimal_povm
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:45:24.366036+00:00
-- url     : https://prove2.me/theorems/edefd566-74ea-4d01-8d17-02db873d6d68
-- title:
--   Optimal covariant POVM for a pure input
-- statement:
--   In the preceding compact finite-dimensional model, use normalized Schmidt data $c_\mu,\lambda_{\mu t},\psi_{\mu t},\phi_{\mu t}$ with absent-sector rank zero. Define
--
--   $$\eta=\bigoplus_\mu\sqrt{d_\mu}\frac{c_\mu}{|c_\mu|}\sum_{t=1}^{r_\mu}\psi_{\mu t}\otimes\phi_{\mu t},\qquad p_{\mathrm{opt}}=\left(\sum_\mu |c_\mu|\sum_{t=1}^{r_\mu}\sqrt{d_\mu\lambda_{\mu t}}\right)^2.$$
--
--   There exists a positive full-space seed whose covariant density is measurable, integrable, integrates to the identity, and satisfies $P_\Psi\Xi P_\Psi=|\eta\rangle\langle\eta|$. Its diagonal density equals $p_{\mathrm{opt}}$ for every group element. Every normalized covariant seed has likelihood at most this value, and equality holds precisely when its compression is the displayed dyad. This states attainment and the complete normalization, including unoccupied multiplicity directions. A phase at an absent sector has no effect.
-- source:
--   Maximum likelihood estimation for a group of physical transformations, arXiv:quant-ph/0507007v1, PDF p. 7, Theorem 1 (optimal POVM), Eqs.(14)–(16)

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

/-- PDF pp.7–8, Theorem 1, Eqs.(14)–(16): full normalized completion exists;
the bound, attained value, and compressed seed are all conclusions. -/
theorem optimal_povm (_finite : FiniteDimensional ℝ E) (_lie : LieGroup 𝓘(ℝ, E) ∞ G)
    (R : FiniteModel G I S) (D : SchmidtInput R) :
    QAlgorithms.IsState D.vector ∧
    (∀ Xi, IsSeed R Xi → likelihood Xi (QAlgorithms.pureDensity D.vector) ≤ D.formula) ∧
    (∃ Xi, IsSeed R Xi ∧
      Measurable (densityOrbit R Xi) ∧ Integrable (densityOrbit R Xi) R.dg ∧
      (∫ g, densityOrbit R Xi g ∂(R.dg)) = 1 ∧
      D.projector * Xi * D.projector = QAlgorithms.pureDensity D.eta ∧
      ∀ g, QAlgorithms.effectProb (densityOrbit R Xi g)
        (densityOrbit R (QAlgorithms.pureDensity D.vector) g) = D.formula) ∧
    (∀ Xi, IsSeed R Xi →
      (likelihood Xi (QAlgorithms.pureDensity D.vector) = D.formula ↔
        D.projector * Xi * D.projector = QAlgorithms.pureDensity D.eta)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P39

end
