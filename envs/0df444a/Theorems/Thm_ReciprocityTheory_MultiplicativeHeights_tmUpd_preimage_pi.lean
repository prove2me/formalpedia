-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_tmUpd_preimage_pi
-- name    : ReciprocityTheory.MultiplicativeHeights.tmUpd_preimage_pi
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:04:43.67262+00:00
-- url     : https://prove2.me/theorems/13bb33dd-85ff-5329-9876-8b160825dd54
-- title:
--   Multiplicative Heights: tm Upd preimage pi
-- statement:
--   The Multiplicative Heights construction uses the tm Upd preimage pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusMeanB.lean#L28-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusMeanB.lean#L28-L41

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanA
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Real Function
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem ReciprocityTheory.MultiplicativeHeights.tmUpd_preimage_pi (i : ι) (s : ι → Set ℝ) :
    tmUpd i ⁻¹' (Set.univ.pi s) = (Set.univ.pi (update s i Set.univ)) ×ˢ s i := by sorry
