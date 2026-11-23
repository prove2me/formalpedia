-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Bridge_HCFR_inf_comp_ne_zero
-- name    : ReciprocityTheory.Neutral.Bridge.HCFR.inf_comp_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:55.1709+00:00
-- url     : https://prove2.me/theorems/55a60512-489b-4784-8c87-9f1048158a6e
-- title:
--   HCFR: inf comp ne zero
-- statement:
--   The HCFR construction uses the inf comp ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/HCFFromRecipB.lean#L85-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/HCFFromRecipB.lean#L85-L88

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

theorem ReciprocityTheory.Neutral.Bridge.HCFR.inf_comp_ne_zero (a : Ideles K) (w : InfinitePlace K) : (a : AdeleRing (𝓞 K) K).1 w ≠ 0 := by sorry
