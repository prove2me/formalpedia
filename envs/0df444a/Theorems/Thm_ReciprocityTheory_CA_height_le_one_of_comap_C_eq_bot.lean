-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_height_le_one_of_comap_C_eq_bot
-- name    : ReciprocityTheory.CA.height_le_one_of_comap_C_eq_bot
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:39:12.531869+00:00
-- url     : https://prove2.me/theorems/43e0f4b1-12a1-5e99-91b3-04939e71ee97
-- title:
--   CA: height le one of comap C eq bot
-- statement:
--   The CA construction uses the height le one of comap C eq bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/SaturatedChains/AlgStep.lean#L9-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/SaturatedChains/AlgStep.lean#L9-L29

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_IsSaturatedChain
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_AlgStep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open Polynomial
attribute [local instance] Polynomial.algebra Polynomial.isLocalization

theorem ReciprocityTheory.CA.height_le_one_of_comap_C_eq_bot {A : Type*} [CommRing A] [IsDomain A]
    (Q : Ideal A[X]) [Q.IsPrime] (hQ : Q.comap C = ⊥) : Q.height ≤ 1 := by sorry
