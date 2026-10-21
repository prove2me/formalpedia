-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P39_external_entanglement_saturation
-- name    : QAlgorithms.Papers.Independent.Next46.P39.external_entanglement_saturation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:52:14.113987+00:00
-- url     : https://prove2.me/theorems/12241180-9511-4e28-a2bd-29782b0a9f4a
-- title:
--   External entanglement saturates at the irrep dimensions
-- statement:
--   For the compact finite-dimensional model, add an inert reference of positive dimension $r$. Suppose $m_\mu r\ge d_\mu$ for every irrep. The canonical representation with multiplicities exactly $d_\mu$ admits an isometric intertwining embedding into the actual $r$-assisted Hilbert space. Moreover, for every positive reference dimension $n$ and every normalized input in that assisted space, its actual cyclic orbit admits an isometric intertwining compression into this canonical representation.
--
--   $$L_n=\sum_\mu d_\mu^2\quad\text{for every }n\ge r.$$
--
--   The value displayed is a universal covariant-measurement bound with pure-state attainment. If already $m_\mu\ge d_\mu$ for every sector, every positive reference dimension has the unassisted likelihood ceiling, so external entanglement is unnecessary. This corrects the reversed inequality in the printed last sentence and retains the orbit-embedding explanation.
-- source:
--   Maximum likelihood estimation for a group of physical transformations, arXiv:quant-ph/0507007v1, PDF p. 12, Theorem 4 (use of external entanglement), corrected printed inequality

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

/-- PDF p.12, Theorem 4 and proof. Printed d_mu>=m_mu in the last sentence
is reversed: the correct condition is m_mu>=d_mu. Saturation includes actual
orbit compression into multiplicity d_mu, and an embedding of that canonical
space into any reference size that has already saturated the multiplicities. -/
theorem external_entanglement_saturation (_finite : FiniteDimensional ℝ E) (_lie : LieGroup 𝓘(ℝ, E) ∞ G)
    (R : FiniteModel G I S) (r : ℕ) (hr : 0 < r)
    (hsat : ∀ s, R.d s ≤ R.m s * r) :
    (∀ n, 0 < n → ∀ psi : EuclideanSpace ℂ (I × Fin n),
      QAlgorithms.IsState psi → CompressesOrbit R n psi) ∧
    (∃ J : Matrix (I × Fin r) (CanonicalIndex R) ℂ,
      Jᴴ * J = 1 ∧ ∀ g v,
        rectAct J (canonicalAction R g v) = QAlgorithms.act (assistedAction R r g) (rectAct J v)) ∧
    (∀ n, r ≤ n → AssistedMaximum R n (∑ s, ((R.d s) ^ 2 : ℕ))) ∧
    ((∀ s, R.d s ≤ R.m s) →
      ∀ n, 0 < n → assistedCeiling R n = ceilingLikelihood R) := by sorry

end QAlgorithms.Papers.Independent.Next46.P39

end
