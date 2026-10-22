-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P10_formation_and_cost_upper_bounds
-- name    : QAlgorithms.Papers.Independent.Gap20.P10.formation_and_cost_upper_bounds
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:29:20.563093+00:00
-- url     : https://prove2.me/theorems/4b6258dd-5089-4148-bb96-1f8a0650995a
-- title:
--   Upper bounds by formation and entanglement cost
-- statement:
--   All Hilbert spaces are finite dimensional and nonzero, all states are positive semidefinite with trace one, and entropies use base-two logarithms with zero eigenvalues contributing zero. Write $E_I$ for one half the infimum of the paired mutual-information increment over all normalized extensions with the required unprimed marginal and arbitrary positive finite primed dimensions.
--
--   For every bipartite state $\rho$, let $E_f(\rho)$ be the pure-state convex roof of the reduced-state entropy and let $E_c(\rho)$ be the operational entanglement cost: the infimum of singlets per copy required for asymptotic LOCC formation with vanishing error. Then
--
--   $$E_I(\rho)\le E_f(\rho),\qquad E_I(\rho)\le E_c(\rho).$$
--
--   Both upper bounds are retained. The accepted operational definition uses deterministic finite LOCC protocols and vanishing Bures error; it does not replace entanglement cost by a single-copy convex roof.
-- source:
--   An additive and operational entanglement measure: conditional entanglement of mutual information, arXiv:0804.3683v2, PDF p. 3, Unnumbered corollary: upper bounds by formation and entanglement cost

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P10

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Claimed50.P33

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.3, corollary after Convexity: both E_I <= E_f and E_I <= E_c.
E_f is the accepted pure convex roof. E_c is the actual asymptotic LOCC
formation cost of singlets, with vanishing Bures error, not single-copy E_f. -/
theorem formation_and_cost_upper_bounds {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hrho : IsDensityMatrix rho) :
    bipartiteCemi rho ≤ Information100.P08.formation rho ∧
      bipartiteCemi rho ≤ Dependency50.P42.entanglementCost Dependency50.P42.paperBures rho := by sorry

end QAlgorithms.Papers.Independent.Gap20.P10

end
