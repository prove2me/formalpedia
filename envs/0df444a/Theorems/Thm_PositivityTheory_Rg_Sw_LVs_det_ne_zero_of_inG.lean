-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_det_ne_zero_of_inG
-- name    : PositivityTheory.Rg.Sw.LVs.det_ne_zero_of_inG
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:03:55.006443+00:00
-- url     : https://prove2.me/theorems/b7fd282b-83cb-52cc-8440-6fd26a1e7426
-- title:
--   LVs: det ne zero of in G
-- statement:
--   The LVs construction uses the det ne zero of in G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/FderivEqZeroOfVanish.lean#L21-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/FderivEqZeroOfVanish.lean#L21-L30

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_HasFDerivAtInt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_Imports
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarDir
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_FderivEqZeroOfVanish
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set Metric Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs.HolB PositivityTheory.Rg.Sw.LVs.HolC
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.LVs.det_ne_zero_of_inG {y : M2 n} (hy : InG y) : y.det ≠ 0 := by sorry
