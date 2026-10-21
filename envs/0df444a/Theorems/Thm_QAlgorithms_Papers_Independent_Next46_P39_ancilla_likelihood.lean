-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P39_ancilla_likelihood
-- name    : QAlgorithms.Papers.Independent.Next46.P39.ancilla_likelihood
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:54:04.778677+00:00
-- url     : https://prove2.me/theorems/63a5deea-d37f-4f15-adbe-27094c28cdc8
-- title:
--   Assisted likelihood and its saturation value
-- statement:
--   For the compact finite-dimensional action with an inert reference of positive dimension $n$, the multiplicities become $m_\mu n$. The exact maximum over states and normalized covariant measurements is
--
--   $$L_n=\sum_\mu d_\mu\min(d_\mu,m_\mu n)\le\sum_\mu d_\mu^2.$$
--
--   The first quantity is a universal bound for every density matrix and is attained by a normalized pure input with a normalized measurement. If $m_\mu n\ge d_\mu$ for every sector, equality with the last sum holds. This gives a representation-generic assisted estimation interface; it does not supply tensor-power fidelity sequences.
-- source:
--   Maximum likelihood estimation for a group of physical transformations, arXiv:quant-ph/0507007v1, PDF p. 12, §3, Eq.(30): assisted likelihood and saturation value

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

/-- PDF p.12, Eq.(30) and preceding paragraph: actual assisted optimum,
with multiplicities m_mu*n, and its saturation value sum d_mu². -/
theorem ancilla_likelihood (_finite : FiniteDimensional ℝ E) (_lie : LieGroup 𝓘(ℝ, E) ∞ G)
    (R : FiniteModel G I S) (n : ℕ) (hn : 0 < n) :
    AssistedMaximum R n (assistedCeiling R n) ∧
    assistedCeiling R n ≤ ∑ s, (R.d s) ^ 2 ∧
    ((∀ s, R.d s ≤ R.m s * n) → assistedCeiling R n = ∑ s, (R.d s) ^ 2) := by sorry

end QAlgorithms.Papers.Independent.Next46.P39

end
