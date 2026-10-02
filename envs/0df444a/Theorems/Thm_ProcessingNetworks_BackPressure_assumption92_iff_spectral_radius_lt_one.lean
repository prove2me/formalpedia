-- Prove2me | Theorems.Thm_ProcessingNetworks_BackPressure_assumption92_iff_spectral_radius_lt_one
-- name    : ProcessingNetworks.BackPressure.assumption92_iff_spectral_radius_lt_one
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T18:22:55.422612+00:00
-- url     : https://prove2.me/theorems/df84c411-5b06-44a3-8c8f-61cc7d46ed7a
-- title:
--   Proposition 9.4 — Assumption 9.2 via basis spectral radius (milestone)
-- statement:
--   **Proposition 9.4.** Given Assumption 9.1, Assumption 9.2 holds iff some basis's associated
--   matrix $Q$ (Eq. 9.3) has spectral radius $< 1$.
--
--   This is the practical criterion for verifying Assumption 9.2: rather than searching over all
--   of $\mathbb{R}^J_+$ for an $x$ with $Rx>0$, one checks a single $I\times I$ matrix's spectral
--   radius. The proof uses the Neumann series $\hat R^{-1} = \Delta^{-1}(I+Q+Q^2+\cdots)$.
--
--   **Formalization note.** Spectral radius is Mathlib's own `spectralRadius` (from
--   `Mathlib.Analysis.Normed.Algebra.Spectrum`), applied to `Matrix (Fin I) (Fin I) ℝ` as a normed
--   $\mathbb{R}$-algebra — genuine substrate reuse, per this mission's own `BRIEF.md`
--   recommendation, rather than defining eigenvalues from scratch.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 165, Proposition 9.4

import Mathlib
import Definitions.Def_ProcessingNetworks_BackPressure_SPNPlanningData
import Definitions.Def_ProcessingNetworks_BackPressure_LeontiefNetwork

namespace ProcessingNetworks.BackPressure

/-- Proposition 9.4, Dai & Harrison p. 165 (PDF p. 181): given that Assumption 9.1 holds,
Assumption 9.2 holds if and only if there is a choice of basis, with associated decomposition
`R̂ = (I-Q)Δ⁻¹` (Eq. 9.3), such that `Q` has spectral radius `< 1`. -/
theorem assumption92_iff_spectral_radius_lt_one
    {I J K : ℕ} (dat : SPNPlanningData I J K) (h91 : SatisfiesAssumption91 dat) :
    SatisfiesAssumption92 dat ↔
      ∃ (basis : ActivityBasis dat) (Q : Matrix (Fin I) (Fin I) ℝ) (Δ : Fin I → ℝ),
        IsBasisDecomposition (basisMatrix basis) Q Δ ∧
        spectralRadius ℝ Q < 1 := by sorry

end ProcessingNetworks.BackPressure
