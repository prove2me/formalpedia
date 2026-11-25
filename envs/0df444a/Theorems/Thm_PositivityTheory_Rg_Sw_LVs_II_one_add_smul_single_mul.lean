-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_one_add_smul_single_mul
-- name    : PositivityTheory.Rg.Sw.LVs.II.one_add_smul_single_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:09:29.708236+00:00
-- url     : https://prove2.me/theorems/da69f2d1-2091-57d7-b4a9-5d3cbf312e7b
-- title:
--   II: one add smul single mul
-- statement:
--   The II construction uses the one add smul single mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DetOneAddSmulSingleSame.lean#L134-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DetOneAddSmulSingleSame.lean#L134-L140

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

theorem PositivityTheory.Rg.Sw.LVs.II.one_add_smul_single_mul (i : Fin n) (u v : ℂ) :
    ((1 : Matrix (Fin n) (Fin n) ℂ) + u • Matrix.single i i 1) * (1 + v • Matrix.single i i 1) =
      1 + (u + v + u * v) • Matrix.single i i 1 := by sorry
