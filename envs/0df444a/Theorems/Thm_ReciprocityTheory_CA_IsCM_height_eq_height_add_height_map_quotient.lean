-- Prove2me | Theorems.Thm_ReciprocityTheory_CA_IsCM_height_eq_height_add_height_map_quotient
-- name    : ReciprocityTheory.CA.IsCM.height_eq_height_add_height_map_quotient
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:13:33.078189+00:00
-- url     : https://prove2.me/theorems/98233e75-e76f-4ce7-a6c9-5299fd69ad72
-- title:
--   Is CM: height eq height add height map quotient
-- statement:
--   The Is CM construction uses the height eq height add height map quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/SaturatedChains/RingKrullDimLocalizationQuotientEqHeight.lean#L283-L313
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/SaturatedChains/RingKrullDimLocalizationQuotientEqHeight.lean#L283-L313

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

theorem ReciprocityTheory.CA.IsCM.height_eq_height_add_height_map_quotient {P : Type*} [CommRing P] [IsLocalRing P]
    (h : IsCM P) (p q : Ideal P) [p.IsPrime] [q.IsPrime] (hpq : p ≤ q) :
    q.height = p.height + (q.map (Ideal.Quotient.mk p)).height := by sorry
