-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_symm_fix
-- name    : PositivityTheory.Rg.Sw.LVs.TC.symm_fix
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:49:42.417919+00:00
-- url     : https://prove2.me/theorems/ccd180c6-7247-47b6-a702-aa263f428aba
-- title:
--   TC: symm fix
-- statement:
--   The TC construction uses the symm fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/TCCalc.lean#L64-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/TCCalc.lean#L64-L80

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

theorem PositivityTheory.Rg.Sw.LVs.TC.symm_fix {F : V → ℂ} {Ω : Set V} (hΩ : IsOpen Ω) (hF : ContDiffOn ℂ ∞ F Ω) {k : ℕ}
    (ih : ∀ c ∈ Ω, ∀ (v : Fin k → V) (σ : Equiv.Perm (Fin k)), iteratedFDeriv ℂ k F c (v ∘ σ) = iteratedFDeriv ℂ k F c v)
    {c : V} (hc : c ∈ Ω) (σ : Equiv.Perm (Fin (k + 1))) (h0 : σ 0 = 0) (v : Fin (k + 1) → V) :
    iteratedFDeriv ℂ (k + 1) F c (v ∘ σ) = iteratedFDeriv ℂ (k + 1) F c v := by sorry
