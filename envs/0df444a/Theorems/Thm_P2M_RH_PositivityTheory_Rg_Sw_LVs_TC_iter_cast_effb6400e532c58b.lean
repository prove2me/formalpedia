-- Prove2me | Theorems.Thm_P2M_RH_PositivityTheory_Rg_Sw_LVs_TC_iter_cast_effb6400e532c58b
-- name    : P2M_RH_PositivityTheory_Rg_Sw_LVs_TC_iter_cast_effb6400e532c58b
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:43:19.453878+00:00
-- url     : https://prove2.me/theorems/24714a54-4489-56f5-afb6-6b555357caf7
-- title:
--   P2 M RH Positivity Theory Rg Sw LVs TC iter cast effb6400e532c58b: P2 M RH Positivity Theory Rg Sw LVs TC iter cast effb6400e532c58b
-- statement:
--   The P2 M RH Positivity Theory Rg Sw LVs TC iter cast effb6400e532c58b construction uses the P2 M RH Positivity Theory Rg Sw LVs TC iter cast effb6400e532c58b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/TCHeights.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/TCHeights.lean#L15-L18

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCBlockA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCHeights
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.TC
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem P2M_RH_PositivityTheory_Rg_Sw_LVs_TC_iter_cast_effb6400e532c58b {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (f : V → ℂ) (x : V) {m m' : ℕ} (h : m = m')
    (v : Fin m → V) : iteratedFDeriv ℂ m f x v = iteratedFDeriv ℂ m' f x (v ∘ Fin.cast h.symm) := by sorry

alias «PositivityTheory».«Rg».«Sw».«LVs».«TC».«iter_cast» := P2M_RH_PositivityTheory_Rg_Sw_LVs_TC_iter_cast_effb6400e532c58b
