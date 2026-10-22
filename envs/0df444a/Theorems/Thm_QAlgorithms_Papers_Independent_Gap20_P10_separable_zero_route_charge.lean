-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P10_separable_zero_route_charge
-- name    : QAlgorithms.Papers.Independent.Gap20.P10.separable_zero_route_charge
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:32:17.150711+00:00
-- url     : https://prove2.me/theorems/c519fe58-2af5-4525-b1cb-4589812036ee
-- title:
--   Separable states admit side information with zero route charge
-- statement:
--   All Hilbert spaces are finite dimensional and nonzero, all states are positive semidefinite with trace one, and entropies use base-two logarithms with zero eigenvalues contributing zero. Write $E_I$ for one half the infimum of the paired mutual-information increment over all normalized extensions with the required unprimed marginal and arbitrary positive finite primed dimensions.
--
--   Let $\rho_{AB}$ be a separable bipartite state. There exist positive finite ancillary dimensions for $A\prime,B\prime,E$ and a normalized pure state $|\Psi\rangle_{AA\prime BB\prime E}$ whose $AB$ marginal is $\rho$, such that
--
--   $$I(AA\prime:BB\prime)_\Psi-I(A\prime:B\prime)_\Psi=0,\qquad Q_I(\Psi)=Q_{II}(\Psi)=0.$$
--
--   Here $Q_I,Q_{II}$ are the displayed entropic charges of Fig.3. This asserts the existence of zero-charge side information and both zero-charge routes, without optimizing an unrestricted signed traffic count.
-- source:
--   An additive and operational entanglement measure: conditional entanglement of mutual information, arXiv:0804.3683v2, PDF p. 4, Unnumbered: separable states admit side information with zero route charge

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P10

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Claimed50.P33

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.3--4, separable-label extension and paragraph after Proposition 2:
a separable input admits finite primed side information and a normalized pure
purification with zero paired increment and zero charges for BOTH displayed
routes. This is existence of a zero-charge route, not operational optimality. -/
theorem separable_zero_route_charge {a b : ℕ} [NeZero a] [NeZero b]
    (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (hrho : IsDensityMatrix rho) (hsep : QAlgorithms.Entanglement.IsSeparableDensity rho) :
    ∃ ap bp e : ℕ, 0 < ap ∧ 0 < bp ∧ 0 < e ∧
      ∃ psi : EuclideanSpace ℂ
        (RegisterBasis (fun i : Fin 5 => Fin ((![a, ap, b, bp, e] : Fin 5 → ℕ) i))),
      ‖psi‖ = 1 ∧ twoRegisterMarginal (pureDensity psi) 0 2 = rho ∧
      routeDifference (pureDensity psi) = 0 ∧
      routeI (pureDensity psi) = 0 ∧ routeII (pureDensity psi) = 0 := by sorry

end QAlgorithms.Papers.Independent.Gap20.P10

end
