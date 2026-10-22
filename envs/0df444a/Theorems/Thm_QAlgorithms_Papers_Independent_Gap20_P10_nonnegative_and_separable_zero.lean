-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P10_nonnegative_and_separable_zero
-- name    : QAlgorithms.Papers.Independent.Gap20.P10.nonnegative_and_separable_zero
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:26:31.198689+00:00
-- url     : https://prove2.me/theorems/6a2b0a26-2bfa-4750-97f6-05bf4743fbef
-- title:
--   Nonnegativity and vanishing on separable states
-- statement:
--   All Hilbert spaces are finite dimensional and nonzero, all states are positive semidefinite with trace one, and entropies use base-two logarithms with zero eigenvalues contributing zero. Write $E_I$ for one half the infimum of the paired mutual-information increment over all normalized extensions with the required unprimed marginal and arbitrary positive finite primed dimensions.
--
--   For every bipartite state $\rho_{AB}$,
--
--   $$E_I(\rho_{AB})\ge0,\qquad \rho_{AB}\text{ separable}\ \Longrightarrow\ E_I(\rho_{AB})=0.$$
--
--   Here separability means a finite convex combination of normalized product states. This is the source’s normalization axiom for an entanglement measure; no converse to the zero-value implication is asserted.
-- source:
--   An additive and operational entanglement measure: conditional entanglement of mutual information, arXiv:0804.3683v2, PDF p. 3, Unnumbered axiom 2: nonnegativity and vanishing on separable states

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P10

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Claimed50.P33

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.3, axiom 2: nonnegative on all states and zero on separable
states. No converse faithfulness assertion is made. -/
theorem nonnegative_and_separable_zero {A B : Type}
    [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho) :
    0 ≤ bipartiteCemi rho ∧
      (QAlgorithms.Entanglement.IsSeparableDensity rho → bipartiteCemi rho = 0) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P10

end
