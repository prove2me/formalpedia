-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CEq_iteratedFDeriv_comp_clm
-- name    : PositivityTheory.Rg.Sw.LVs.CEq.iteratedFDeriv_comp_clm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:46:17.149858+00:00
-- url     : https://prove2.me/theorems/9fb90dde-9d49-45fc-80ba-0a130e2b77d5
-- title:
--   CEq: iterated FDeriv comp clm
-- statement:
--   The CEq construction uses the iterated FDeriv comp clm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/CayleyEq.lean#L16-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/CayleyEq.lean#L16-L33

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_CayleyA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_CayleyEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.CEq
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
omit [DecidableEq ι] [DecidableEq κ]

theorem PositivityTheory.Rg.Sw.LVs.CEq.iteratedFDeriv_comp_clm (F : Matrix κ κ ℂ → ℂ) (hF : AnalyticAt ℂ F 0)
    (L : Matrix ι ι ℂ →L[ℂ] Matrix κ κ ℂ) (n : ℕ) (v : Fin n → Matrix ι ι ℂ) :
    iteratedFDeriv ℂ n (F ∘ L) 0 v = iteratedFDeriv ℂ n F 0 (fun i => L (v i)) := by sorry
