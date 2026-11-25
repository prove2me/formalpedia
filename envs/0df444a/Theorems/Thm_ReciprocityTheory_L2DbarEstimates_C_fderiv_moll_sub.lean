-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_fderiv_moll_sub
-- name    : ReciprocityTheory.L2DbarEstimates.C.fderiv_moll_sub
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:53:49.38304+00:00
-- url     : https://prove2.me/theorems/cf4ac089-c7c4-5620-bebc-35099bbab01e
-- title:
--   C: fderiv moll sub
-- statement:
--   The C construction uses the fderiv moll sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/RegConv.lean#L41-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/RegConv.lean#L41-L51

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_IntegralBumpProfOnePos
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_RegConv
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

theorem ReciprocityTheory.L2DbarEstimates.C.fderiv_moll_sub {n : ℕ} {t : ℝ} (x y w : V n) :
    fderiv ℝ (fun y => ((moll n t (x - y) : ℝ) : ℂ)) y w
      = -((fderiv ℝ (moll n t) (x - y) w : ℝ) : ℂ) := by sorry
