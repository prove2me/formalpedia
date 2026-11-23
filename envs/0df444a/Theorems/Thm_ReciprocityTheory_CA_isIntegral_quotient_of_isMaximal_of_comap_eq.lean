-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_isIntegral_quotient_of_isMaximal_of_comap_eq
-- name    : ReciprocityTheory.CA.isIntegral_quotient_of_isMaximal_of_comap_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:00:23.458918+00:00
-- url     : https://prove2.me/theorems/dc0f3d97-5607-41d6-becd-b970c92243b6
-- title:
--   CA: is Integral quotient of is Maximal of comap eq
-- statement:
--   The CA construction uses the is Integral quotient of is Maximal of comap eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/PolynomialHeights/PolyMax.lean#L9-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/PolynomialHeights/PolyMax.lean#L9-L35

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_ChainConnInDim
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_PolyMax
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open Polynomial IsLocalRing
variable {P : Type*} [CommRing P] [IsLocalRing P]

theorem ReciprocityTheory.CA.isIntegral_quotient_of_isMaximal_of_comap_eq {S : Type*} [CommRing S] [Algebra P S]
    [Algebra.FiniteType P S] (𝔑 : Ideal S) [𝔑.IsMaximal]
    (h : 𝔑.comap (algebraMap P S) = maximalIdeal P) : Algebra.IsIntegral P (S ⧸ 𝔑) := by sorry
