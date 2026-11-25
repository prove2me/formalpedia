-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_mul_proj_apply
-- name    : PositivityTheory.Rg.Sw.LVs.mul_proj_apply
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:58:44.069809+00:00
-- url     : https://prove2.me/theorems/8f53d91c-011c-4946-8cd5-b60f47b4853a
-- title:
--   LVs: mul proj apply
-- statement:
--   The LVs construction uses the mul proj apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DpDual.lean#L81-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DpDual.lean#L81-L95

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DpDual
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
open scoped ContDiff ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.LVs.mul_proj_apply {m : Type} [Fintype m] (s : Finset (Fin n)) (X : Matrix m s ℂ) (d : m) (b : Fin n) :
    (X * proj s) d b = if h : b ∈ s then X d ⟨b, h⟩ else 0 := by sorry
