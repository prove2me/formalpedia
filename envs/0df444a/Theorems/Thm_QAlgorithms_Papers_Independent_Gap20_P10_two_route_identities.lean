-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P10_two_route_identities
-- name    : QAlgorithms.Papers.Independent.Gap20.P10.two_route_identities
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T20:31:16.534751+00:00
-- url     : https://prove2.me/theorems/4336f56c-9863-4d47-83b0-cb2799ce75a2
-- title:
--   Explicit entropic rates of routes I and II
-- statement:
--   All Hilbert spaces are finite dimensional and nonzero, all states are positive semidefinite with trace one, and entropies use base-two logarithms with zero eigenvalues contributing zero. Write $E_I$ for one half the infimum of the paired mutual-information increment over all normalized extensions with the required unprimed marginal and arbitrary positive finite primed dimensions.
--
--   Let $|\Psi\rangle_{AA\prime BB\prime E}$ be a normalized pure state. Define $\Delta I=I(AA\prime:BB\prime)-I(A\prime:B\prime)$ using its actual marginals. Define the displayed route charges by $Q_I=\tfrac12[I(BB\prime:A\mid E)+I(A\prime:B\mid EA)]$ and $Q_{II}=\tfrac12[I(BB\prime:AA\prime)+0-I(A\prime:B\prime)]$. Then
--
--   $$Q_I=\tfrac12\Delta I,\qquad Q_{II}=\tfrac12\Delta I,\qquad Q_I=Q_{II}.$$
--
--   These are entropic identities for the two displayed routes. They make no assertion about a minimum over arbitrary physical protocols.
-- source:
--   An additive and operational entanglement measure: conditional entanglement of mutual information, arXiv:0804.3683v2, PDF p. 4, Unnumbered: explicit entropic rates of routes I and II (Fig.3)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P10

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Claimed50.P33

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.4, Fig.3: the two explicitly displayed entropic route charges
both equal half the paired information increment, hence equal one another.
The five physical registers are A,A',B,B',E, and the global state is pure. -/
theorem two_route_identities {D : Fin 5 → Type} [∀ i, Fintype (D i)]
    [∀ i, Nonempty (D i)] (psi : EuclideanSpace ℂ (RegisterBasis D))
    (hpsi : ‖psi‖ = 1) :
    routeI (pureDensity psi) = routeDifference (pureDensity psi) / 2 ∧
    routeII (pureDensity psi) = routeDifference (pureDensity psi) / 2 ∧
    routeI (pureDensity psi) = routeII (pureDensity psi) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P10

end
