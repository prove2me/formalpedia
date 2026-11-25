-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_HSt_MI_hasDerivAt_curve
-- name    : PositivityTheory.Rg.Sw.HSt.MI.hasDerivAt_curve
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:50.796631+00:00
-- url     : https://prove2.me/theorems/d4f828eb-74d1-464f-b9e7-8a3560fe1d07
-- title:
--   MI: has Deriv At curve
-- statement:
--   The MI construction uses the has Deriv At curve property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/CayleyCosetSums/MatInv.lean#L57-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/CayleyCosetSums/MatInv.lean#L57-L62

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IILeft
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_CayleyCosetSums_MatInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Set Filter Topology
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.MI
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.HSt.MI.hasDerivAt_curve (x Z : M2 n) :
    HasDerivAt (fun t : ℝ => x * NormedSpace.exp ((t : ℂ) • Z)) (x * Z) 0 := by sorry
