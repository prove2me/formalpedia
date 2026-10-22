-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P10_multipartite_additivity
-- name    : QAlgorithms.Papers.Independent.Gap20.P10.multipartite_additivity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:33:12.563124+00:00
-- url     : https://prove2.me/theorems/f2a60eab-4d54-46c3-ac17-9bbf8417010d
-- title:
--   Proposition 3: multipartite additivity
-- statement:
--   All Hilbert spaces are finite dimensional and nonzero, all states are positive semidefinite with trace one, and entropies use base-two logarithms with zero eigenvalues contributing zero. Write $E_I$ for one half the infimum of the paired mutual-information increment over all normalized extensions with the required unprimed marginal and arbitrary positive finite primed dimensions.
--
--   Let $n\ge2$, and let $\rho_{A_1\cdots A_n}$ and $\sigma_{B_1\cdots B_n}$ be arbitrary states. Use total mutual information $I_n=\sum_i S(A_i)-S(A_1\cdots A_n)$ and the half-infimum definition of $E_I$, with one unrestricted paired ancilla per party. Then
--
--   $$E_I(A_1B_1:\cdots:A_nB_n)_{\rho\otimes\sigma}=E_I(A_1:\cdots:A_n)_\rho+E_I(B_1:\cdots:B_n)_\sigma.$$
--
--   The independent tensor product is constructed and grouped party by party. The factor remains $1/2$ for every $n$, and at two parties this recovers bipartite additivity.
-- source:
--   An additive and operational entanglement measure: conditional entanglement of mutual information, arXiv:0804.3683v2, PDF p. 4, Proposition 3: multipartite additivity

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P10

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P10

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Claimed50.P33

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Proposition 3, PDF p.4: multipartite additivity of the half-infimum
of TOTAL information, with the product paired party by party and n>=2. -/
theorem multipartite_additivity {n : ℕ} (hn : 2 ≤ n)
    {D F : Fin n → Type} [∀ i, Fintype (D i)] [∀ i, Fintype (F i)]
    [∀ i, Nonempty (D i)] [∀ i, Nonempty (F i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ)
    (sigma : Matrix (RegisterBasis F) (RegisterBasis F) ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    cemi (partyProduct rho sigma) = cemi rho + cemi sigma := by sorry

end QAlgorithms.Papers.Independent.Gap20.P10

end
