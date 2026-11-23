-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Bridge_HCFR_infIdele_snd
-- name    : ReciprocityTheory.Neutral.Bridge.HCFR.infIdele_snd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:21:54.752027+00:00
-- url     : https://prove2.me/theorems/7edc5bbd-4561-4918-ba50-290dbc6bec50
-- title:
--   HCFR: inf Idele snd
-- statement:
--   The HCFR construction uses the inf Idele snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/HCFFromRecipB.lean#L31-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/HCFFromRecipB.lean#L31-L32

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

theorem ReciprocityTheory.Neutral.Bridge.HCFR.infIdele_snd (w : InfinitePlace K) (x : (w.Completion)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    (infIdele K w x : AdeleRing (𝓞 K) K).2 v = 1 := by sorry
