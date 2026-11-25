-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_moll_conv_symm
-- name    : ReciprocityTheory.L2DbarEstimates.C.moll_conv_symm
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:01:14.538705+00:00
-- url     : https://prove2.me/theorems/b40635dd-dd5c-4ad6-a7f9-14f85be20c33
-- title:
--   C: moll conv symm
-- statement:
--   The C construction uses the moll conv symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/RegIndep.lean#L47-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/RegIndep.lean#L47-L56

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_MeasurableEmbeddingRotAbout
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_RegConv
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_RegIndep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal

theorem ReciprocityTheory.L2DbarEstimates.C.moll_conv_symm (n : ℕ) (s t : ℝ) (x y : V n) :
    ∫ w, moll n s (x - w) * moll n t (w - y) = ∫ w, moll n t (x - w) * moll n s (w - y) := by sorry
