-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_mollify_mollify_swap
-- name    : ReciprocityTheory.L2DbarEstimates.C.mollify_mollify_swap
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:54:50.879597+00:00
-- url     : https://prove2.me/theorems/96f3eace-8451-5283-a8ae-7facd18d9cc5
-- title:
--   C: mollify mollify swap
-- statement:
--   The C construction uses the mollify mollify swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/RegIndep.lean#L12-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/RegIndep.lean#L12-L45

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

theorem ReciprocityTheory.L2DbarEstimates.C.mollify_mollify_swap {n : ℕ} {u : V n → ℂ} (hu : Integrable u) {s t : ℝ} (hs : 0 < s)
    (ht : 0 < t) (x : V n) :
    ∫ w, (moll n s (x - w) : ℂ) * ∫ y, (moll n t (w - y) : ℂ) * u y =
      ∫ y, ((∫ w, moll n s (x - w) * moll n t (w - y) : ℝ) : ℂ) * u y := by sorry
