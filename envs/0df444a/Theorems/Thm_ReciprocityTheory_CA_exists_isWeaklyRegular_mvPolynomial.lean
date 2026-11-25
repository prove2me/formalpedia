-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_exists_isWeaklyRegular_mvPolynomial
-- name    : ReciprocityTheory.CA.exists_isWeaklyRegular_mvPolynomial
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:38:14.832967+00:00
-- url     : https://prove2.me/theorems/3c9dff1c-a2c9-5180-9be9-6c3a34e28aa4
-- title:
--   CA: exists is Weakly Regular mv Polynomial
-- statement:
--   The CA construction uses the exists is Weakly Regular mv Polynomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/PolynomialHeights/PolySeq.lean#L8-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/PolynomialHeights/PolySeq.lean#L8-L71

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_PolyStep
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_PolyMax
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_PolySeq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open IsLocalRing RingTheory.Sequence

theorem ReciprocityTheory.CA.exists_isWeaklyRegular_mvPolynomial {P : Type*} [CommRing P] [IsLocalRing P] {rs : List P}
    (hmem : ∀ r ∈ rs, r ∈ maximalIdeal P) (hrs : IsWeaklyRegular P rs) (N : ℕ)
    (𝔑 : Ideal (MvPolynomial (Fin N) P)) [𝔑.IsMaximal]
    (h : 𝔑.comap MvPolynomial.C = maximalIdeal P) :
    ∃ ss : List (MvPolynomial (Fin N) P), ss.length = rs.length + N ∧ (∀ s ∈ ss, s ∈ 𝔑) ∧
      IsWeaklyRegular (MvPolynomial (Fin N) P) ss := by sorry
