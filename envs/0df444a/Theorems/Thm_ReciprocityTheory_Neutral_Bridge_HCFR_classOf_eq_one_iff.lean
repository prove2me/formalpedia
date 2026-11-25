-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Bridge_HCFR_classOf_eq_one_iff
-- name    : ReciprocityTheory.Neutral.Bridge.HCFR.classOf_eq_one_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:43:44.029112+00:00
-- url     : https://prove2.me/theorems/75d17cb5-8ed7-4eee-866c-53dad4602fb6
-- title:
--   HCFR: class Of eq one iff
-- statement:
--   The HCFR construction uses the class Of eq one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/HCFFromRecipA.lean#L156-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/HCFFromRecipA.lean#L156-L196

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HilbertClassFieldA
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HCFFromRecipA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1
open scoped nonZeroDivisors
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Bridge ReciprocityTheory.Neutral.Bridge.HCFR
variable (K : Type) [Field K] [NumberField K]

theorem ReciprocityTheory.Neutral.Bridge.HCFR.classOf_eq_one_iff (a : Ideles K) :
    classOf K a = 1 ↔ ∃ k : Kˣ, ∃ u ∈ rayUnits K ⊤ ∅, a = diagUnits K k * u := by sorry
