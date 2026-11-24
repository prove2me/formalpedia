-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_T_rpow_neg_le_add
-- name    : PositivityTheory.Rg.Sw.WR.T.rpow_neg_le_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:08:24.655856+00:00
-- url     : https://prove2.me/theorems/d6998bd6-43fe-4ea8-8039-a74a30cc1382
-- title:
--   T: rpow neg le add
-- statement:
--   The T construction uses the rpow neg le add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ContinuousHerm.lean#L45-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ContinuousHerm.lean#L45-L54

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DifferentiableOfTop
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousHerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.T
open PositivityTheory.Rg.Sw
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.WR.T.rpow_neg_le_add (x a a0 d : ℝ) (hx : 0 < x) (ha : |a - a0| ≤ d) :
    x ^ (-a) ≤ x ^ (-(a0 - d)) + x ^ (-(a0 + d)) := by sorry
