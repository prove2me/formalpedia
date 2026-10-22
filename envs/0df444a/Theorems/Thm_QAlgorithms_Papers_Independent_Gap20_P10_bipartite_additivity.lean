-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P10_bipartite_additivity
-- name    : QAlgorithms.Papers.Independent.Gap20.P10.bipartite_additivity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:23:54.277103+00:00
-- url     : https://prove2.me/theorems/c4cfb8da-522a-45ad-97e1-d8b63ee986a6
-- title:
--   Proposition 1: bipartite additivity
-- statement:
--   All Hilbert spaces are finite dimensional and nonzero, all states are positive semidefinite with trace one, and entropies use base-two logarithms with zero eigenvalues contributing zero. Write $E_I$ for one half the infimum of the paired mutual-information increment over all normalized extensions with the required unprimed marginal and arbitrary positive finite primed dimensions.
--
--   Let $\rho_{AB}$ and $\sigma_{CD}$ be arbitrary bipartite states. Form their tensor product and group the local systems as $AC:BD$. Then
--
--   $$E_I(AC:BD)_{\rho\otimes\sigma}=E_I(A:B)_\rho+E_I(C:D)_\sigma.$$
--
--   This is exact additivity on independent resources; the left cut retains the corresponding local systems together.
-- source:
--   An additive and operational entanglement measure: conditional entanglement of mutual information, arXiv:0804.3683v2, PDF p. 3, Proposition 1: bipartite additivity (the page-1 seed pinned to its numbered theorem)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P10

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Claimed50.P33

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Proposition 1, PDF p.3 (abstract seed p.1): bipartite additivity across
AC:BD for the constructed product rho_AB tensor sigma_CD. -/
theorem bipartite_additivity {A B C D : Type}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]
    (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix (C × D) (C × D) ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    bipartiteCemi (regroupedProduct rho sigma) =
      bipartiteCemi rho + bipartiteCemi sigma := by sorry

end QAlgorithms.Papers.Independent.Gap20.P10

end
