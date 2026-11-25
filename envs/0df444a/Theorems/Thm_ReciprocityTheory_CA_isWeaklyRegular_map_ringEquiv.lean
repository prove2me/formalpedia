-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_isWeaklyRegular_map_ringEquiv
-- name    : ReciprocityTheory.CA.isWeaklyRegular_map_ringEquiv
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:38:24.275+00:00
-- url     : https://prove2.me/theorems/9b23e9d0-d700-46bb-a894-93e394041074
-- title:
--   CA: is Weakly Regular map ring Equiv
-- statement:
--   The CA construction uses the is Weakly Regular map ring Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/PolynomialHeights/PolyStep.lean#L37-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/PolynomialHeights/PolyStep.lean#L37-L48

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

theorem ReciprocityTheory.CA.isWeaklyRegular_map_ringEquiv {S T : Type*} [CommRing S] [CommRing T] (e : S ≃+* T)
    {rs : List S} (hrs : IsWeaklyRegular S rs) : IsWeaklyRegular T (rs.map e) := by sorry
