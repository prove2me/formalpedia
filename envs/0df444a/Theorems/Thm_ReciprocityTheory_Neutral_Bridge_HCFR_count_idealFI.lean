-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Bridge_HCFR_count_idealFI
-- name    : ReciprocityTheory.Neutral.Bridge.HCFR.count_idealFI
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:04:45.236895+00:00
-- url     : https://prove2.me/theorems/0b28c101-cedc-527b-b8af-b5f4b7623b98
-- title:
--   HCFR: count ideal FI
-- statement:
--   The HCFR construction uses the count ideal FI property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/HCFFromRecipA.lean#L110-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/HCFFromRecipA.lean#L110-L111

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

theorem ReciprocityTheory.Neutral.Bridge.HCFR.count_idealFI (v : HeightOneSpectrum (𝓞 K)) (a : Ideles K) :
    FractionalIdeal.count K v (idealFI K a) = ordAt K v a := by sorry
