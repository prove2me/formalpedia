-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_small_dimensions_dominate
-- name    : QAlgorithms.Papers.Independent.Information100.P62.small_dimensions_dominate
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T21:42:16.488549+00:00
-- url     : https://prove2.me/theorems/95ff8166-d411-4038-9338-a7bdb4a030e0
-- title:
--   Proposition 4.4: minimum dimensions for non-domination
-- statement:
--   Every channel $\Phi:L(H)\to L(K)$ on positive finite-dimensional spaces admits a dominating transmittable algebra whenever
--   $$\min\{\dim H,\dim K\}\le2\quad\text{or}\quad\dim H=\dim K=3.$$
--   The second alternative is specifically the square three-dimensional case.
-- source:
--   Transmitting algebras through quantum channels, arXiv:2609.40054v1, PDF p. 31, Proposition 4.4: minimum dimensions for non-domination

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

namespace QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.31, 32, Proposition 4.4: minimum dimensions for non-domination. -/
theorem small_dimensions_dominate [Nonempty I] [Nonempty O]
    (F : Superop I O) (hF : IsChannel F)
    (hdim : min (Fintype.card I) (Fintype.card O) ≤ 2 ∨
      Fintype.card I = 3 ∧ Fintype.card O = 3) : HasDominating F := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P62
