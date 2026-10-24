-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P10_strong_superadditivity
-- name    : QAlgorithms.Papers.Independent.Gap20.P10.strong_superadditivity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T20:30:22.208236+00:00
-- url     : https://prove2.me/theorems/fb531be2-3202-4f80-b6e0-63826cac377b
-- title:
--   Strong superadditivity
-- statement:
--   All Hilbert spaces are finite dimensional and nonzero, all states are positive semidefinite with trace one, and entropies use base-two logarithms with zero eigenvalues contributing zero. Write $E_I$ for one half the infimum of the paired mutual-information increment over all normalized extensions with the required unprimed marginal and arbitrary positive finite primed dimensions.
--
--   Let $\tau_{ACBD}$ be an arbitrary four-party state, and let $\tau_{AB}$ and $\tau_{CD}$ be its corresponding reduced states. Then
--
--   $$E_I(AC:BD)_\tau\ge E_I(A:B)_{\tau_{AB}}+E_I(C:D)_{\tau_{CD}}.$$
--
--   No product premise is imposed on $\tau$. This is the strong superadditivity supplied by the telescoping information difference in equation (5), which underlies the lower inequality in Proposition 1.
-- source:
--   An additive and operational entanglement measure: conditional entanglement of mutual information, arXiv:0804.3683v2, PDF p. 3, Unnumbered: strong superadditivity underlying Proposition 1

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P10

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Claimed50.P33

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.3, equation (5) and the super-additivity paragraph: arbitrary
four-party input, without a product hypothesis. -/
theorem strong_superadditivity {A B C D : Type}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]
    (tau : Matrix ((A × C) × (B × D)) ((A × C) × (B × D)) ℂ)
    (htau : IsDensityMatrix tau) :
    bipartiteCemi (Dependency50.P21.marginalAB
      (fun (x y : A × (B × (C × D))) =>
        tau ((x.1, x.2.2.1), (x.2.1, x.2.2.2))
          ((y.1, y.2.2.1), (y.2.1, y.2.2.2)))) +
      bipartiteCemi (marginalCD tau) ≤ bipartiteCemi tau := by sorry

end QAlgorithms.Papers.Independent.Gap20.P10

end
