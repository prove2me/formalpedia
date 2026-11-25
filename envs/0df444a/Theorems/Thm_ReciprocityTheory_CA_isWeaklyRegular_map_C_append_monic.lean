-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_isWeaklyRegular_map_C_append_monic
-- name    : ReciprocityTheory.CA.isWeaklyRegular_map_C_append_monic
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:38:20.015769+00:00
-- url     : https://prove2.me/theorems/ed5b60ea-a00f-45e7-a2f0-8e9f6c5a9912
-- title:
--   CA: is Weakly Regular map C append monic
-- statement:
--   The CA construction uses the is Weakly Regular map C append monic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/PolynomialHeights/PolyStep.lean#L17-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/PolynomialHeights/PolyStep.lean#L17-L35

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_ChainConnInDim
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_PolyStep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open Polynomial RingTheory.Sequence

theorem ReciprocityTheory.CA.isWeaklyRegular_map_C_append_monic {S : Type*} [CommRing S] {rs : List S}
    (hrs : IsWeaklyRegular S rs) {g : S[X]} (hg : g.Monic) :
    IsWeaklyRegular S[X] (rs.map C ++ [g]) := by sorry
