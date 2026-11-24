-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_minorOn_inv_of_unitary
-- name    : PositivityTheory.Rg.Sw.LVs.minorOn_inv_of_unitary
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:59:59.81502+00:00
-- url     : https://prove2.me/theorems/3f315052-e47e-4289-99be-0a54fa4584d3
-- title:
--   LVs: minor On inv of unitary
-- statement:
--   The LVs construction uses the minor On inv of unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/ScalarSectionCompactBlockInvariant.lean#L180-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/ScalarSectionCompactBlockInvariant.lean#L180-L183

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulConjTransposeEq
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
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
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.LVs.minorOn_inv_of_unitary {u : Matrix (Fin n) (Fin n) ℂ} (hu : u ∈ unitaryGroup (Fin n) ℂ) (s : Finset (Fin n)) :
    minorOn s u⁻¹ = star (minorOn s u) := by sorry
