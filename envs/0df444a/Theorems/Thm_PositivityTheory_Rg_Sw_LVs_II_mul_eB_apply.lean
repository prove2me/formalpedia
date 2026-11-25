-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_mul_eB_apply
-- name    : PositivityTheory.Rg.Sw.LVs.II.mul_eB_apply
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:02:53.405822+00:00
-- url     : https://prove2.me/theorems/29e11d86-788a-57d4-a595-ec50762a3917
-- title:
--   II: mul e B apply
-- statement:
--   The II construction uses the mul e B apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/FderivXZxSkew.lean#L107-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/FderivXZxSkew.lean#L107-L108

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_InfInvA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_FderivXZxSkew
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.II
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.LVs.II.mul_eB_apply (M : M2 n) (a b : Fin n) : (M * eB a b) (Sum.inr a) (Sum.inl b) = -M (Sum.inr a) (Sum.inr a) := by sorry
