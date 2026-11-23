-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Bridge_HCFR_diag_comp
-- name    : ReciprocityTheory.Neutral.Bridge.HCFR.diag_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:21:35.09974+00:00
-- url     : https://prove2.me/theorems/01e0344e-e120-4eb6-acae-28e2bbdc0f31
-- title:
--   HCFR: diag comp
-- statement:
--   The HCFR construction uses the diag comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/HCFFromRecipA.lean#L143-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/HCFFromRecipA.lean#L143-L144

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

theorem ReciprocityTheory.Neutral.Bridge.HCFR.diag_comp (k : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v ((diagUnits K k : AdeleRing (𝓞 K) K).2 v) = v.valuation K (k : K) := by sorry
