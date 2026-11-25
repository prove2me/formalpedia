-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_height_le_height_comap_C_add_one
-- name    : ReciprocityTheory.CA.height_le_height_comap_C_add_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:38:37.095987+00:00
-- url     : https://prove2.me/theorems/d7411a6e-1fa7-40cb-9daa-aa83ed8d9889
-- title:
--   CA: height le height comap C add one
-- statement:
--   The CA construction uses the height le height comap C add one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/SaturatedChains/AlgStep.lean#L31-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/SaturatedChains/AlgStep.lean#L31-L55

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

theorem ReciprocityTheory.CA.height_le_height_comap_C_add_one {R : Type*} [CommRing R] [IsNoetherianRing R]
    (P : Ideal R[X]) [P.IsPrime] : P.height ≤ (P.comap C).height + 1 := by sorry
