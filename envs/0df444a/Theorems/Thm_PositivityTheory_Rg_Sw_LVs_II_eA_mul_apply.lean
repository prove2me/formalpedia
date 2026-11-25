-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_eA_mul_apply
-- name    : PositivityTheory.Rg.Sw.LVs.II.eA_mul_apply
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:58:29.747655+00:00
-- url     : https://prove2.me/theorems/8f8139fe-7f99-4b29-9e01-b52840678c87
-- title:
--   II: e A mul apply
-- statement:
--   The II construction uses the e A mul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/FderivXZxSkew.lean#L98-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/FderivXZxSkew.lean#L98-L99

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

theorem PositivityTheory.Rg.Sw.LVs.II.eA_mul_apply (M : M2 n) (a b : Fin n) : (eA a b * M) (Sum.inr a) (Sum.inr b) = M (Sum.inr b) (Sum.inr b) := by sorry
