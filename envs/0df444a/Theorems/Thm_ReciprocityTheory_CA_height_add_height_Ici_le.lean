-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_height_add_height_Ici_le
-- name    : ReciprocityTheory.CA.height_add_height_Ici_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:38:50.56643+00:00
-- url     : https://prove2.me/theorems/039e68ab-770a-48d4-b5df-eaa4075e431e
-- title:
--   CA: height add height Ici le
-- statement:
--   The CA construction uses the height add height Ici le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/SaturatedChains/RingKrullDimLocalizationQuotientEqHeight.lean#L8-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/SaturatedChains/RingKrullDimLocalizationQuotientEqHeight.lean#L8-L52

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

theorem ReciprocityTheory.CA.height_add_height_Ici_le {α : Type*} [PartialOrder α] {a b : α} (hab : a ≤ b) :
    Order.height a + Order.height (⟨b, hab⟩ : Set.Ici a) ≤ Order.height b := by sorry
