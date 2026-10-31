-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P47_isometric_compression
-- name    : QAlgorithms.Papers.Independent.Intake100.P47.isometric_compression
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:23:35.970664+00:00
-- url     : https://prove2.me/theorems/fef0c480-a1c7-4eef-bb68-1640117252d2
-- title:
--   Lemma 2: Isometric compression of divergences
-- statement:
--   All Hilbert spaces are finite dimensional and nonzero. States are positive semidefinite operators of trace one, logarithms are natural, and $\rho\ll\sigma$ means inclusion of supports. Write $D_\alpha$ and $\widetilde D_\alpha$ for the Petz and sandwiched divergences, respectively, with generalized inverse powers on support and orders $0,1,\infty$ defined by limits. Let $\rho\in\mathcal S(A)$, $\sigma\in\mathcal S(A')$, and let $U:A\to A'$ be an isometry. Then
--   $$D_\alpha(\rho\|U^\dagger\sigma U)\le D_\alpha(U\rho U^\dagger\|\sigma)\quad(0\le\alpha\le2),$$
--   $$\widetilde D_\alpha(\rho\|U^\dagger\sigma U)\le\widetilde D_\alpha(U\rho U^\dagger\|\sigma)\quad(1/2\le\alpha<\infty).$$
--   The compressed comparison need not have trace one. These inequalities permit compression to marginal supports without assuming invertibility.
-- source:
--   Correlation Detection and an Operational Interpretation of the Renyi Mutual Information, arXiv:1408.6894v5, PDF p. 6, Lemma 2: Isometric compression of divergences

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P47

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P47

open scoped BigOperators Matrix ComplexOrder ComplexConjugate Topology

open Filter QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P22 (Op mixed)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Dependency50.P28 (SupportLE pinch logNonnegativeExtended)

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy IsSupported)

open QAlgorithms.Papers.Independent.Bridge50.P49 (groupedProduct)

open QAlgorithms.Papers.Independent.Claimed50.P12 (DiagonalIn)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D I J : Type}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype I] [Fintype J]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

variable [DecidableEq I] [DecidableEq J]

/-- arXiv:1408.6894v5, PDF p.6, Lemma 2, (2.10)--(2.11).
The compressed comparison U^dagger sigma U is PSD but need not be normalized. -/
theorem isometric_compression [Nonempty I] [Nonempty J]
    (rho : Op I) (sigma : Op J) (hr : IsDensityMatrix rho) (hs : IsDensityMatrix sigma)
    (U : Matrix J I ℂ) (hU : Uᴴ * U = 1) :
    (∀ a : ℝ, 0 ≤ a → a ≤ 2 →
      completedRenyiDivergence false (a : RenyiOrder) rho (Uᴴ * sigma * U) ≤ completedRenyiDivergence false (a : RenyiOrder) (U * rho * Uᴴ) sigma) ∧
    (∀ a : ℝ, (1/2 : ℝ) ≤ a →
      completedRenyiDivergence true (a : RenyiOrder) rho (Uᴴ * sigma * U) ≤ completedRenyiDivergence true (a : RenyiOrder) (U * rho * Uᴴ) sigma) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P47

end
