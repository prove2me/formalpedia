-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_HSt_MI_contDiff_entry
-- name    : PositivityTheory.Rg.Sw.HSt.MI.contDiff_entry
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:59:25.770019+00:00
-- url     : https://prove2.me/theorems/26d5a4ef-05df-4dbf-ab7c-8f03fa4dd7e0
-- title:
--   MI: cont Diff entry
-- statement:
--   The MI construction uses the cont Diff entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/CayleyCosetSums/MatInv.lean#L17-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/CayleyCosetSums/MatInv.lean#L17-L20

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

theorem PositivityTheory.Rg.Sw.HSt.MI.contDiff_entry (a b : Fin n ⊕ Fin n) : ContDiff ℝ ∞ (fun x : M2 n => x a b) := by sorry
