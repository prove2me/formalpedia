-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_isMaximal_comap_of_isMaximal_of_comap_eq
-- name    : ReciprocityTheory.CA.isMaximal_comap_of_isMaximal_of_comap_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:39:15.270273+00:00
-- url     : https://prove2.me/theorems/7da4ce8e-5770-5ea7-bab5-dea961e79986
-- title:
--   CA: is Maximal comap of is Maximal of comap eq
-- statement:
--   The CA construction uses the is Maximal comap of is Maximal of comap eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/PolynomialHeights/PolyMax.lean#L37-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/PolynomialHeights/PolyMax.lean#L37-L56

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

theorem ReciprocityTheory.CA.isMaximal_comap_of_isMaximal_of_comap_eq {S' S : Type*} [CommRing S'] [CommRing S]
    [Algebra P S'] [Algebra P S] [Algebra S' S] [IsScalarTower P S' S] [Algebra.FiniteType P S]
    (𝔑 : Ideal S) [𝔑.IsMaximal] (h : 𝔑.comap (algebraMap P S) = maximalIdeal P) :
    (𝔑.comap (algebraMap S' S)).IsMaximal := by sorry
