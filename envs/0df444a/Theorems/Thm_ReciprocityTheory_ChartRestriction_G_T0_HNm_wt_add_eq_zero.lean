-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_HNm_wt_add_eq_zero
-- name    : ReciprocityTheory.ChartRestriction.G.T0.HNm.wt_add_eq_zero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:36:41.909884+00:00
-- url     : https://prove2.me/theorems/bed9049d-ae8d-511a-b2a0-c76257eb38a4
-- title:
--   HNm: wt add eq zero
-- statement:
--   The HNm construction uses the wt add eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HNormA.lean#L7-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HNormA.lean#L7-L17

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open ReciprocityTheory.ChartRestriction.G.T0.HNm

theorem ReciprocityTheory.ChartRestriction.G.T0.HNm.wt_add_eq_zero {a b : WithTop ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a + b = 0) : a = 0 := by sorry
