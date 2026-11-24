-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Bridge_HCFR_ordAt_diag
-- name    : ReciprocityTheory.Neutral.Bridge.HCFR.ordAt_diag
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:44:01.663864+00:00
-- url     : https://prove2.me/theorems/5f8b9bb6-eedd-4601-a65b-017705569720
-- title:
--   HCFR: ord At diag
-- statement:
--   The HCFR construction uses the ord At diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/HCFFromRecipA.lean#L146-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/HCFFromRecipA.lean#L146-L149

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

theorem ReciprocityTheory.Neutral.Bridge.HCFR.ordAt_diag (k : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    ordAt K v (diagUnits K k) = -WithZero.log (v.valuation K (k : K)) := by sorry
