-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_symm_swap
-- name    : PositivityTheory.Rg.Sw.LVs.TC.symm_swap
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:49:38.787099+00:00
-- url     : https://prove2.me/theorems/149cbd37-5be4-4186-8e85-e5e4a7b2a968
-- title:
--   TC: symm swap
-- statement:
--   The TC construction uses the symm swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/TCCalc.lean#L88-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/TCCalc.lean#L88-L103

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

theorem PositivityTheory.Rg.Sw.LVs.TC.symm_swap {F : V → ℂ} {Ω : Set V} (hΩ : IsOpen Ω) (hF : ContDiffOn ℂ ∞ F Ω) {k : ℕ}
    {c : V} (hc : c ∈ Ω) (v : Fin (k + 2) → V) :
    iteratedFDeriv ℂ (k + 2) F c (v ∘ Equiv.swap 0 1) = iteratedFDeriv ℂ (k + 2) F c v := by sorry
