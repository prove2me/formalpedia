-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_height_add_height_map_quotient_le
-- name    : ReciprocityTheory.CA.height_add_height_map_quotient_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:03:25.429512+00:00
-- url     : https://prove2.me/theorems/649a8e6e-a834-5cc9-ae68-eaea4ba1a6a0
-- title:
--   CA: height add height map quotient le
-- statement:
--   The CA construction uses the height add height map quotient le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/SaturatedChains/RingKrullDimLocalizationQuotientEqHeight.lean#L65-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/SaturatedChains/RingKrullDimLocalizationQuotientEqHeight.lean#L65-L95

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_IsSaturatedChain
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_LocDim
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_RingKrullDimLocalizationQuotientEqHeight
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

theorem ReciprocityTheory.CA.height_add_height_map_quotient_le {P : Type*} [CommRing P] (p q : Ideal P) [p.IsPrime]
    [q.IsPrime] (hpq : p ≤ q) : p.height + (q.map (Ideal.Quotient.mk p)).height ≤ q.height := by sorry
