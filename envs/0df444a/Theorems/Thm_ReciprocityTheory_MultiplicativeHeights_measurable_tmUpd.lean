-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_measurable_tmUpd
-- name    : ReciprocityTheory.MultiplicativeHeights.measurable_tmUpd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:02:08.902159+00:00
-- url     : https://prove2.me/theorems/749e17ea-ed17-45df-8f54-d36bb6a7ee86
-- title:
--   Multiplicative Heights: measurable tm Upd
-- statement:
--   The Multiplicative Heights construction uses the measurable tm Upd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusMeanB.lean#L20-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusMeanB.lean#L20-L26

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

theorem ReciprocityTheory.MultiplicativeHeights.measurable_tmUpd (i : ι) : Measurable (tmUpd i) := by sorry
