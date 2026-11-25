-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_incl_mul_apply
-- name    : PositivityTheory.Rg.Sw.LVs.incl_mul_apply
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:59:20.674524+00:00
-- url     : https://prove2.me/theorems/573533d6-bbf7-4041-bb0d-ff61ab3a1bcd
-- title:
--   LVs: incl mul apply
-- statement:
--   The LVs construction uses the incl mul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DpDual.lean#L65-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DpDual.lean#L65-L79

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

theorem PositivityTheory.Rg.Sw.LVs.incl_mul_apply {m : Type} [Fintype m] (s : Finset (Fin n)) (X : Matrix s m ℂ) (a : Fin n) (d : m) :
    (dp_incl s * X) a d = if h : a ∈ s then X ⟨a, h⟩ d else 0 := by sorry
