-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_top_vanish
-- name    : PositivityTheory.Rg.Sw.LVs.TC.top_vanish
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:49:23.003823+00:00
-- url     : https://prove2.me/theorems/f4b99365-6391-47c6-9d07-6c5e98507f66
-- title:
--   TC: top vanish
-- statement:
--   The TC construction uses the top vanish property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/TopCompB.lean#L60-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/TopCompB.lean#L60-L91

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TopCompB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.TC

theorem PositivityTheory.Rg.Sw.LVs.TC.top_vanish {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {k : ℕ} {ι : Type*} [Fintype ι]
    (A : ContinuousMultilinearMap ℂ (fun _ : Fin k => V) ℂ) (sg : ι → ℂ) (Y : ι → Fin k → Fin 3 → V)
    (h : ∀ θ : ℝ, ∑ σ, sg σ * A (fun i => Y σ i 0 + Complex.exp (2 * θ * Complex.I) • Y σ i 1 +
      Complex.exp (2 * θ * Complex.I) ^ 2 • Y σ i 2) = 0) :
    ∑ σ, sg σ * A (fun i => Y σ i 2) = 0 := by sorry
