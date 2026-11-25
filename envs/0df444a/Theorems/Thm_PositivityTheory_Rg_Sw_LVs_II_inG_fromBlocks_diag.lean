-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_inG_fromBlocks_diag
-- name    : PositivityTheory.Rg.Sw.LVs.II.inG_fromBlocks_diag
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:58:40.917331+00:00
-- url     : https://prove2.me/theorems/608ad86f-fc44-4018-a04f-1e4f6cdfcd21
-- title:
--   II: in G from Blocks diag
-- statement:
--   The II construction uses the in G from Blocks diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DetOneAddSmulSingleSame.lean#L57-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DetOneAddSmulSingleSame.lean#L57-L61

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_InfInvA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DetOneAddSmulSingleSame
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology
open scoped ContDiff ComplexConjugate
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.II
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.LVs.II.inG_fromBlocks_diag (a d : Matrix (Fin n) (Fin n) ℂ) (h1 : aᴴ * d = 1) (h2 : dᴴ * a = 1) :
    InG (fromBlocks a 0 0 d) := by sorry
