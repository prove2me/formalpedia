-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_HSt_MI_contDiff_adjugate
-- name    : PositivityTheory.Rg.Sw.HSt.MI.contDiff_adjugate
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:55:20.057273+00:00
-- url     : https://prove2.me/theorems/71cefd85-3d48-4124-b63b-7af64423c151
-- title:
--   MI: cont Diff adjugate
-- statement:
--   The MI construction uses the cont Diff adjugate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/CayleyCosetSums/MatInv.lean#L36-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/CayleyCosetSums/MatInv.lean#L36-L44

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

theorem PositivityTheory.Rg.Sw.HSt.MI.contDiff_adjugate : ContDiff ℝ ∞ (fun x : M2 n => x.adjugate) := by sorry
