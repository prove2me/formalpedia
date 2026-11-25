-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Bridge_HCFR_ordAt_localIdele
-- name    : ReciprocityTheory.Neutral.Bridge.HCFR.ordAt_localIdele
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:04:59.039633+00:00
-- url     : https://prove2.me/theorems/c6abeb2d-33b9-4c0e-b3a3-adc93fe14f65
-- title:
--   HCFR: ord At local Idele
-- statement:
--   The HCFR construction uses the ord At local Idele property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/HCFFromRecipA.lean#L276-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/HCFFromRecipA.lean#L276-L289

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
open Classical

theorem ReciprocityTheory.Neutral.Bridge.HCFR.ordAt_localIdele (v w : HeightOneSpectrum (𝓞 K)) (π : (v.adicCompletion K)ˣ)
    (hπ : IsUniformiserAt K v (π : v.adicCompletion K)) :
    ordAt K w (localIdele K v π) = if w = v then 1 else 0 := by sorry
