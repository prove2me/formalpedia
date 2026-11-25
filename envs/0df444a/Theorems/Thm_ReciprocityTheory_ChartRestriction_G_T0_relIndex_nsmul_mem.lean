-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_relIndex_nsmul_mem
-- name    : ReciprocityTheory.ChartRestriction.G.T0.relIndex_nsmul_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:38:55.853891+00:00
-- url     : https://prove2.me/theorems/d9572eaf-f3bb-56ad-bebe-580168b20486
-- title:
--   T0: rel Index nsmul mem
-- statement:
--   The T0 construction uses the rel Index nsmul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ExistsNeZeroMemNormSqLeGramDetDivRelIndex.lean#L91-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ExistsNeZeroMemNormSqLeGramDetDivRelIndex.lean#L91-L93

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TransferenceA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ExistsNeZeroMemNormSqLeGramDetDivRelIndex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open Module Submodule Matrix

theorem ReciprocityTheory.ChartRestriction.G.T0.relIndex_nsmul_mem {E : Type*} [AddCommGroup E] (H L : AddSubgroup E) {x : E}
    (hx : x ∈ L) : H.relIndex L • x ∈ H := by sorry
