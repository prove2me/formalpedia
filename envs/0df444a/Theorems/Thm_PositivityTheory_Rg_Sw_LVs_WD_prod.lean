-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_WD_prod
-- name    : PositivityTheory.Rg.Sw.LVs.WD_prod
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:50:22.240889+00:00
-- url     : https://prove2.me/theorems/f2d6474c-13c6-480c-aa9c-8c26b44045f2
-- title:
--   LVs: WD prod
-- statement:
--   The LVs construction uses the WD prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/ContDiffOnSecondCayleyBlockEntries.lean#L163-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/ContDiffOnSecondCayleyBlockEntries.lean#L163-L170

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ContDiffOnSecondCayleyBlockEntries
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem PositivityTheory.Rg.Sw.LVs.WD_prod (Q R Q' R' : Matrix (Fin n) (Fin n) ℂ) :
    (Cm n * fromBlocks 0 Q R 0 * (Cm n)⁻¹) * (Cm n * fromBlocks 0 Q' R' 0 * (Cm n)⁻¹) =
      Cm n * fromBlocks (Q * R') 0 0 (R * Q') * (Cm n)⁻¹ := by sorry
