-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_isCM_localization_mvPolynomial
-- name    : ReciprocityTheory.CA.isCM_localization_mvPolynomial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:50.084046+00:00
-- url     : https://prove2.me/theorems/7d296ab6-4cab-4ded-89e8-b07fac9ec0e8
-- title:
--   CA: is CM localization mv Polynomial
-- statement:
--   The CA construction uses the is CM localization mv Polynomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/PolynomialHeights/PolyCM.lean#L8-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/PolynomialHeights/PolyCM.lean#L8-L37

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_PolySeq
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_RingKrullDimLocalizationQuotientEqHeight
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_PolyCM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open IsLocalRing

theorem ReciprocityTheory.CA.isCM_localization_mvPolynomial {P : Type*} [CommRing P] [IsLocalRing P] (hP : IsCM P) (N : ℕ)
    (𝔑 : Ideal (MvPolynomial (Fin N) P)) [𝔑.IsMaximal]
    (h : 𝔑.comap MvPolynomial.C = maximalIdeal P) :
    IsCM (Localization.AtPrime 𝔑) ∧ (𝔑.height : WithBot ℕ∞) = ringKrullDim P + N := by sorry
