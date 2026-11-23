-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Bridge_HCFR_infIdele_fst_ne
-- name    : ReciprocityTheory.Neutral.Bridge.HCFR.infIdele_fst_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:10:49.045797+00:00
-- url     : https://prove2.me/theorems/60996ca5-dab0-45c2-a9df-a8936caae2c8
-- title:
--   HCFR: inf Idele fst ne
-- statement:
--   The HCFR construction uses the inf Idele fst ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/HCFFromRecipB.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/HCFFromRecipB.lean#L26-L29

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

theorem ReciprocityTheory.Neutral.Bridge.HCFR.infIdele_fst_ne (w w' : InfinitePlace K) (h : w' ≠ w) (x : (w.Completion)ˣ) :
    (infIdele K w x : AdeleRing (𝓞 K) K).1 w' = 1 := by sorry
