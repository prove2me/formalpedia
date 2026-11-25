-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_pstep_monic_mem_of_mul
-- name    : ReciprocityTheory.CA.pstep_monic_mem_of_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:38:42.965737+00:00
-- url     : https://prove2.me/theorems/9430fa50-e5a9-4f09-97b5-4ae57ee58869
-- title:
--   CA: pstep monic mem of mul
-- statement:
--   The CA construction uses the pstep monic mem of mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/PolynomialHeights/PolyStep.lean#L7-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/PolynomialHeights/PolyStep.lean#L7-L15

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

theorem ReciprocityTheory.CA.pstep_monic_mem_of_mul {S : Type*} [CommRing S] (J : Ideal S) {g h : S[X]} (hg : g.Monic)
    (hgh : g * h ∈ J.map (C : S →+* S[X])) : h ∈ J.map (C : S →+* S[X]) := by sorry
