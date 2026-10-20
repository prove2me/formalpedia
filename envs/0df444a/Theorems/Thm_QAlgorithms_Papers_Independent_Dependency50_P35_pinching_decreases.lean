-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P35_pinching_decreases
-- name    : QAlgorithms.Papers.Independent.Dependency50.P35.pinching_decreases
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:09:45.525453+00:00
-- url     : https://prove2.me/theorems/43c6896d-0b7a-4262-9acd-accebeccc89f
-- title:
--   Proposition 14: pinching decreases divergence
-- statement:
--   Let $\rho,\sigma\ge0$ with $\rho\ne0$, and let $\alpha\in(0,1)\cup(1,\infty)$. Choose any orthonormal eigenbasis $\{u_k\}$ diagonalizing $\sigma$, put $P_k=|u_k\rangle\langle u_k|$, and define $\mathcal E_\sigma(\rho)=\sum_k P_k\rho P_k$. Then
--
--   $$
--   \widetilde D_\alpha(\mathcal E_\sigma(\rho)\|\sigma)\le\widetilde D_\alpha(\rho\|\sigma).
--   $$
--
--   The choice within repeated eigenspaces is arbitrary; these are rank-one projectors. Singular $\sigma$, including zero, and all positive orders except one remain in the domain.
-- source:
--   On quantum Renyi entropies: a new generalization and some properties, arXiv:1306.3142v4, PDF p. 17, Proposition 14

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Dependency50.P35

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the accepted matrix type and positive-operator Schatten expression.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat schatten)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

/-- PDF p.17, Proposition 14: an arbitrary orthonormal eigenbasis, including
rank-one refinements of degenerate eigenspaces and the case sigma=0. -/
theorem pinching_decreases {I : Type} [Fintype I] [DecidableEq I]
    (a : ℝ) (ha : 0 < a ∧ a ≠ 1) (rho sigma U : Mat I)
    (hr : rho.PosSemidef) (hs : sigma.PosSemidef) (hn : rho ≠ 0)
    (hU : Uᴴ * U = 1 ∧ U * Uᴴ = 1)
    (hdiag : ∃ d : I → ℝ, Uᴴ * sigma * U = Matrix.diagonal (fun i => (d i : ℂ))) :
    divergence a (pinch U rho) sigma ≤ divergence a rho sigma := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P35

end
