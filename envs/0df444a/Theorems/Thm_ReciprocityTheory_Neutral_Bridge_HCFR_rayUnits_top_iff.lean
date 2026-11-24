-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Bridge_HCFR_rayUnits_top_iff
-- name    : ReciprocityTheory.Neutral.Bridge.HCFR.rayUnits_top_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:43:31.054611+00:00
-- url     : https://prove2.me/theorems/21ec995b-d4fd-401b-b370-229e71ef3265
-- title:
--   HCFR: ray Units top iff
-- statement:
--   The HCFR construction uses the ray Units top iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/HCFFromRecipA.lean#L72-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/HCFFromRecipA.lean#L72-L82

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

theorem ReciprocityTheory.Neutral.Bridge.HCFR.rayUnits_top_iff (u : Ideles K) :
    u ∈ rayUnits K ⊤ ∅ ↔ ∀ v : HeightOneSpectrum (𝓞 K), Valued.v ((u : AdeleRing (𝓞 K) K).2 v) = 1 := by sorry
