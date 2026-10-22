-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P10_convexity
-- name    : QAlgorithms.Papers.Independent.Gap20.P10.convexity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:28:11.428211+00:00
-- url     : https://prove2.me/theorems/1e16d3ba-400d-41ed-a472-e183b189312a
-- title:
--   Convexity
-- statement:
--   All Hilbert spaces are finite dimensional and nonzero, all states are positive semidefinite with trace one, and entropies use base-two logarithms with zero eigenvalues contributing zero. Write $E_I$ for one half the infimum of the paired mutual-information increment over all normalized extensions with the required unprimed marginal and arbitrary positive finite primed dimensions.
--
--   Let $\rho$ and $\sigma$ be arbitrary bipartite states on the same local spaces, and let $0\le\lambda\le1$. Then
--
--   $$E_I\bigl(\lambda\rho+(1-\lambda)\sigma\bigr)\le\lambda E_I(\rho)+(1-\lambda)E_I(\sigma).$$
--
--   This bounds the entanglement of a probabilistic mixture by the average of the two entanglements. The extensions optimized for the two inputs may have independently chosen ancillary dimensions.
-- source:
--   An additive and operational entanglement measure: conditional entanglement of mutual information, arXiv:0804.3683v2, PDF p. 3, Unnumbered: convexity

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P10

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Claimed50.P33

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.3, Convexity: both arbitrary input states are on the same space;
ancillary dimensions in their CEMI infima are independently unrestricted. -/
theorem convexity {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (rho sigma : Matrix (A × B) (A × B) ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (lambda : ℝ) (hlambda : 0 ≤ lambda ∧ lambda ≤ 1) :
    bipartiteCemi ((lambda : ℂ) • rho + ((1 - lambda : ℝ) : ℂ) • sigma) ≤
      lambda * bipartiteCemi rho + (1 - lambda) * bipartiteCemi sigma := by sorry

end QAlgorithms.Papers.Independent.Gap20.P10

end
