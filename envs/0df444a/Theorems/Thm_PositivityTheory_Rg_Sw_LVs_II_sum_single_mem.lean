-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_sum_single_mem
-- name    : PositivityTheory.Rg.Sw.LVs.II.sum_single_mem
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:50:29.291667+00:00
-- url     : https://prove2.me/theorems/9c24da3b-bd62-4aba-898d-d3c8a0085471
-- title:
--   II: sum single mem
-- statement:
--   The II construction uses the sum single mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DetOneAddSmulSingleSame.lean#L227-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DetOneAddSmulSingleSame.lean#L227-L230

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

theorem PositivityTheory.Rg.Sw.LVs.II.sum_single_mem (W : Submodule ℂ (M2 n)) (Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] M2 n)
    (h : ∀ i j a, Φ (Matrix.single i j a) ∈ W) (M : Matrix (Fin n) (Fin n) ℂ) : Φ M ∈ W := by sorry
