-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_extC_isRadical
-- name    : ReciprocityTheory.AnForm.R.extC_isRadical
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:23:26.305395+00:00
-- url     : https://prove2.me/theorems/7dad8bfb-62b9-4acd-b000-c513c1a9d456
-- title:
--   R: ext C is Radical
-- statement:
--   The R construction uses the ext C is Radical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/BaseChangeC.lean#L13-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/BaseChangeC.lean#L13-L25

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCB
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial
variable {σ : Type} [Fintype σ]

theorem ReciprocityTheory.AnForm.R.extC_isRadical (𝔭 : Ideal (MvPolynomial σ ℚ)) [𝔭.IsPrime] : (extC 𝔭).IsRadical := by sorry
