-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Bridge_HCFR_eq_of_count
-- name    : ReciprocityTheory.Neutral.Bridge.HCFR.eq_of_count
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:05:12.814906+00:00
-- url     : https://prove2.me/theorems/9001cf3a-e1c6-4b5d-8095-72bc5060c33b
-- title:
--   HCFR: eq of count
-- statement:
--   The HCFR construction uses the eq of count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/HCFFromRecipA.lean#L120-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/HCFFromRecipA.lean#L120-L124

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

theorem ReciprocityTheory.Neutral.Bridge.HCFR.eq_of_count {I J : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), FractionalIdeal.count K v I = FractionalIdeal.count K v J) : I = J := by sorry
