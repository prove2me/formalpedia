-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P01_random_measurement_covering
-- name    : QAlgorithms.Papers.Independent.Intake100.P01.random_measurement_covering
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:55:43.064834+00:00
-- url     : https://prove2.me/theorems/f2f234b8-64d8-4e4f-8531-7805ada0fdf2
-- title:
--   Proposition 10 (Random measurement gives covering)
-- statement:
--   Let $|\psi\rangle_{ABR}$ be a finite pure source with $S(R)<S(B)$. There is a sufficiently small typicality width $\delta_0>0$ such that for every fixed $0<\delta<\delta_0$ and every $\epsilon>0$, all sufficiently large positive $n$ have a nonzero jointly typical projection
--   $$|\Omega_n\rangle=(\Pi_R\otimes\Pi_A\otimes\Pi_B)|\psi\rangle^{\otimes n},\qquad |\Psi_n\rangle=|\Omega_n\rangle/\|\Omega_n\|.$$
--   A Haar-random complete rank-one measurement on the actual typical $A$ subspace has
--   $$\mathbb E_U\sum_jp_j\|\rho^j_R-\rho_R\|_1\le\epsilon,$$
--   where both $\rho_R$ and the conditional marginals come from $\Psi_n$. A coisometry identifies the typical subspace with its finite rank; all source/reference coordinates are retained. This supplies the covering estimate used for helper measurements.
-- source:
--   Quantum state merging and negative information, arXiv:quant-ph/0512247v1, PDF p. 15, Proposition 10 (Random measurement gives covering)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P01

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P01

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

open MeasureTheory

open QAlgorithms.Papers.Independent.Gap20.P11 (IsLOCC productApply finTransport referenceInformation)

open QAlgorithms.Papers.Independent.Bridge50.P40
  (RankMergingCode OneWayMergingCode mergingFidelity SourceProtocolAchievable)

open QAlgorithms.Papers.Independent.Dependency50.P19
  (first marginalRA marginalRB motherTarget motherOutput sourceCopies swap mutualInformation)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalEntropy)

open QAlgorithms.Papers.Independent.Information100.P32 (purity)

open QAlgorithms.Papers.Independent.Advance50.P29 (weakTypicalProjector)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.15, Proposition 10: the expectation is outside the weighted
sum of norms for the COMPUTED normalized projected source. The typicality
width is chosen relative to the strict entropy gap, not arbitrarily large. -/
theorem random_measurement_covering {A B R : Type}
    [Fintype A] [Fintype B] [Fintype R] [Nonempty A] [Nonempty B] [Nonempty R]
    (psi : EuclideanSpace ℂ (R × (A × B))) (hpsi : IsState psi)
    (hgap : vnEntropy (traceRight (pureDensity psi)) <
      vnEntropy (traceLeft (traceLeft (pureDensity psi)))) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ ∀ delta : ℝ, 0 < delta → delta < delta0 →
      ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 < n →
        0 < ‖typicalOmega psi delta n‖ ∧ IsState (normalizedTypicalSource psi delta n) ∧
        let Pi := weakTypicalProjector (traceRight (traceLeft (pureDensity psi))) delta n
        let d := Matrix.rank Pi
        0 < d ∧ ∃ V : Matrix (Fin d) (Fin n → A) ℂ,
          Vᴴ * V = Pi ∧ V * Vᴴ = 1 ∧
          Integrable (fun U => mergingDecouplingError (pureDensity (normalizedTypicalSource psi delta n))
            (coveringRows V U)) (Schur.unitaryHaar d) ∧
          (∫ U, mergingDecouplingError (pureDensity (normalizedTypicalSource psi delta n))
            (coveringRows V U) ∂(Schur.unitaryHaar d)) ≤ eps := by sorry

end QAlgorithms.Papers.Independent.Intake100.P01

end
