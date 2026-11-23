-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Bridge_HCFR_infIdele_fst_self
-- name    : ReciprocityTheory.Neutral.Bridge.HCFR.infIdele_fst_self
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:10:39.787588+00:00
-- url     : https://prove2.me/theorems/3e1cf37c-72cc-4fda-9685-3ba4fcd1ac53
-- title:
--   HCFR: inf Idele fst self
-- statement:
--   The HCFR construction uses the inf Idele fst self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/HCFFromRecipB.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/HCFFromRecipB.lean#L21-L24

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HCFFromRecipA
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HCFFromRecipB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Bridge ReciprocityTheory.Neutral.Bridge.HCFR
variable (K : Type) [Field K] [NumberField K]

theorem ReciprocityTheory.Neutral.Bridge.HCFR.infIdele_fst_self (w : InfinitePlace K) (x : (w.Completion)ˣ) :
    (infIdele K w x : AdeleRing (𝓞 K) K).1 w = x := by sorry
