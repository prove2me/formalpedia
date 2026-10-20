-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P35_divergence_order_monotone
-- name    : QAlgorithms.Papers.Independent.Dependency50.P35.divergence_order_monotone
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:56:43.189263+00:00
-- url     : https://prove2.me/theorems/62b775fe-f7eb-4b5e-b8e2-e29c6aa95268
-- title:
--   Theorem 7 (Monotonicity)
-- statement:
--   Let $\rho,\sigma\ge0$ be finite-dimensional operators with $\rho\ne0$. If $0<\alpha\le\beta$, $\alpha\ne1$, and $\beta\ne1$, then
--
--   $$
--   \widetilde D_\alpha(\rho\|\sigma)\le\widetilde D_\beta(\rho\|\sigma).
--   $$
--
--   This comparison uses extended-real values, includes orders on opposite sides of one, and imposes no support-domination or trace-one assumption. It is monotonicity on the full domain of Definition 2.
-- source:
--   On quantum Renyi entropies: a new generalization and some properties, arXiv:1306.3142v4, PDF p. 10, Theorem 7 (Monotonicity)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Dependency50.P35

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the accepted matrix type and positive-operator Schatten expression.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat schatten)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

/-- PDF p.10, Theorem 7: orders can straddle one; no support assumption is added. -/
theorem divergence_order_monotone {I : Type} [Fintype I] [DecidableEq I]
    (a b : ℝ) (ha : 0 < a ∧ a ≠ 1) (hb : 0 < b ∧ b ≠ 1) (hab : a ≤ b)
    (rho sigma : Mat I) (hr : rho.PosSemidef) (hs : sigma.PosSemidef) (hn : rho ≠ 0) :
    divergence a rho sigma ≤ divergence b rho sigma := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P35

end
