-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_iter_cast
-- name    : PositivityTheory.Rg.Sw.LVs.TC.iter_cast
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:49:41.407804+00:00
-- url     : https://prove2.me/theorems/a16346c2-ba9c-45f0-9196-b0c3196c0694
-- title:
--   TC: iter cast
-- statement:
--   The TC construction uses the iter cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/TCCalc.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/TCCalc.lean#L25-L27

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TopCompS
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCCalc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ContDiff
open Set Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.TC
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem PositivityTheory.Rg.Sw.LVs.TC.iter_cast {F : V → ℂ} {c : V} {m m' : ℕ} (h : m = m') (v : Fin m → V) :
    iteratedFDeriv ℂ m F c v = iteratedFDeriv ℂ m' F c (v ∘ Fin.cast h.symm) := by sorry
