-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_HSt_MI_contDiff_of_entries
-- name    : PositivityTheory.Rg.Sw.HSt.MI.contDiff_of_entries
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:44:30.358044+00:00
-- url     : https://prove2.me/theorems/48df8f87-c63e-4191-8f57-22bea03ac601
-- title:
--   MI: cont Diff of entries
-- statement:
--   The MI construction uses the cont Diff of entries property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/CayleyCosetSums/MatInv.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/CayleyCosetSums/MatInv.lean#L22-L26

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IILeft
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_CayleyCosetSums_MatInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Set Filter Topology
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.MI
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.HSt.MI.contDiff_of_entries {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → M2 n}
    (h : ∀ a b, ContDiff ℝ ∞ fun x => f x a b) : ContDiff ℝ ∞ f := by sorry
