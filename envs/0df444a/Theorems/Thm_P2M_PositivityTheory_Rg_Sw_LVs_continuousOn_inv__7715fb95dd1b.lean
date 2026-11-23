-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LVs_continuousOn_inv__7715fb95dd1b
-- name    : P2M_PositivityTheory_Rg_Sw_LVs_continuousOn_inv__7715fb95dd1b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:39:02.447094+00:00
-- url     : https://prove2.me/theorems/e2cc92d7-b03b-4e37-beb3-3241b689f0f6
-- title:
--   P2 M Positivity Theory Rg Sw LVs continuous On inv  7715fb95dd1b: P2 M Positivity Theory Rg Sw LVs continuous On inv  7715fb95dd1b
-- statement:
--   The P2 M Positivity Theory Rg Sw LVs continuous On inv  7715fb95dd1b construction uses the P2 M Positivity Theory Rg Sw LVs continuous On inv  7715fb95dd1b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/ScalarSectionCompactBlockInvariant.lean#L60-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/ScalarSectionCompactBlockInvariant.lean#L60-L65

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

theorem P2M_PositivityTheory_Rg_Sw_LVs_continuousOn_inv__7715fb95dd1b {m : Type} [Fintype m] [DecidableEq m] :
    ContinuousOn (fun x : Matrix m m ℂ => x⁻¹) {x | x.det ≠ 0} := by sorry

alias «PositivityTheory».«Rg».«Sw».«LVs».«continuousOn_inv'» := P2M_PositivityTheory_Rg_Sw_LVs_continuousOn_inv__7715fb95dd1b
