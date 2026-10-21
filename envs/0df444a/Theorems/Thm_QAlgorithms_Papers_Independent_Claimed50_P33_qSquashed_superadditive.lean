-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P33_qSquashed_superadditive
-- name    : QAlgorithms.Papers.Independent.Claimed50.P33.qSquashed_superadditive
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:39:56.021353+00:00
-- url     : https://prove2.me/theorems/fc8628e0-0c77-4ed2-a4f2-29f3058b647a
-- title:
--   §IV.C equation (49): q-squashed superadditivity
-- statement:
--   Let $m\ge2$ and let $\rho_{12}$ be an arbitrary normalized state of two $m$-party systems, grouped by corresponding parties. Let $\rho_1,\rho_2$ be its two marginals. For the unrestricted extension infimum, without $1/2$, and either $F=I_m$ or $F=S_m$,
--
--   $$E_F^q(\rho_{12})\ge E_F^q(\rho_1)+E_F^q(\rho_2).$$
--
--   The joint state need not be a product. The direction follows the explicit equation (49), correcting the introductory word “subadditive” on PDF p.5.
-- source:
--   Squashed entanglement for multipartite states and entanglement measures based on the mixed convex roof, arXiv:0704.2236v3, PDF p. 6, §IV.C equation (49): q-squashed superadditivity

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P33

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Section IV.C, PDF p.6,(49): superadditivity. The p.5 word
"subadditive" is a prose typo; follow the displayed inequality and proof. -/
theorem qSquashed_superadditive {m : ℕ} (hm : 2 ≤ m)
    {D F : Fin m → Type} [∀ i, Fintype (D i)] [∀ i, Fintype (F i)]
    [∀ i, Nonempty (D i)] [∀ i, Nonempty (F i)]
    (rho : Matrix (RegisterBasis (fun i => D i × F i)) (RegisterBasis (fun i => D i × F i)) ℂ)
    (hrho : IsDensityMatrix rho) : ∀ kind : InformationKind,
      multipartiteSquashed false kind (unprimedMarginal rho) +
        multipartiteSquashed false kind (primedMarginal rho) ≤ multipartiteSquashed false kind rho := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P33

end
