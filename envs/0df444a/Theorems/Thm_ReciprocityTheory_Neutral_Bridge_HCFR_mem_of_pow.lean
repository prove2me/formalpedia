-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Bridge_HCFR_mem_of_pow
-- name    : ReciprocityTheory.Neutral.Bridge.HCFR.mem_of_pow
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:39:39.494072+00:00
-- url     : https://prove2.me/theorems/f74cc9b6-8364-4069-b327-62d538852b34
-- title:
--   HCFR: mem of pow
-- statement:
--   The HCFR construction uses the mem of pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/HCFFromRecipB.lean#L147-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/HCFFromRecipB.lean#L147-L174

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

theorem ReciprocityTheory.Neutral.Bridge.HCFR.mem_of_pow (N : Subgroup (Ideles K)) (m : ℕ) (hm : 0 < m) (hpow : ∀ x : Ideles K, x ^ m ∈ N)
    (hneg : ∀ w : InfinitePlace K, w.IsReal → infIdele K w (-1) ∈ N)
    (a : Ideles K) (ha : (a : AdeleRing (𝓞 K) K).2 = 1) : a ∈ N := by sorry
