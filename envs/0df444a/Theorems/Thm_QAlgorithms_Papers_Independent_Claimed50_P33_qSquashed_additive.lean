-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P33_qSquashed_additive
-- name    : QAlgorithms.Papers.Independent.Claimed50.P33.qSquashed_additive
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T12:31:42.42098+00:00
-- url     : https://prove2.me/theorems/366a8e17-62ea-4ee2-9dbe-aa0328b0fa85
-- title:
--   Proposition 4 / abstract: additivity of both multipartite q-squashed entanglements
-- statement:
--   Let $m\ge2$ and let $\rho$ and $\sigma$ be normalized states on finite nonzero local Hilbert spaces, with possibly different local dimensions. For $F=I_m$ and for $F=S_m$, define $E^q_F$ as the infimum of $F(A_1:\cdots:A_m\mid E)$ over every normalized extension and every positive finite dimension of $E$, without a factor $1/2$. Pair corresponding parties in the tensor product. Then
--
--   $$E^q_F(\rho\otimes\sigma)=E^q_F(\rho)+E^q_F(\sigma).$$
--
--   This is additivity of both multipartite quantum squashed measures.
-- source:
--   Squashed entanglement for multipartite states and entanglement measures based on the mixed convex roof, arXiv:0704.2236v3, PDF p. 6, Proposition 4 / abstract: additivity of both multipartite q-squashed entanglements

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P33

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Proposition 4, PDF p.6,(48), promised in the abstract p.1:
both q quantities, allowing unequal local dimensions. -/
theorem qSquashed_additive {m : ℕ} (hm : 2 ≤ m)
    {D F : Fin m → Type} [∀ i, Fintype (D i)] [∀ i, Fintype (F i)]
    [∀ i, Nonempty (D i)] [∀ i, Nonempty (F i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (sigma : Matrix (RegisterBasis F) (RegisterBasis F) ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    ∀ kind : InformationKind,
      multipartiteSquashed false kind (partyProduct rho sigma) =
      multipartiteSquashed false kind rho + multipartiteSquashed false kind sigma := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P33

end
