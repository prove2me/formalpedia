-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Bridge_HCFR_valued_eq_exp_of_isUniformiserAt
-- name    : ReciprocityTheory.Neutral.Bridge.HCFR.valued_eq_exp_of_isUniformiserAt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:04.339547+00:00
-- url     : https://prove2.me/theorems/008ab303-2035-48e3-9fc8-4f2127ef0f32
-- title:
--   HCFR: valued eq exp of is Uniformiser At
-- statement:
--   The HCFR construction uses the valued eq exp of is Uniformiser At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/HCFFromRecipA.lean#L224-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/HCFFromRecipA.lean#L224-L273

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

theorem ReciprocityTheory.Neutral.Bridge.HCFR.valued_eq_exp_of_isUniformiserAt (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K)
    (hx : IsUniformiserAt K v x) : Valued.v x = WithZero.exp (-1 : ℤ) := by sorry
