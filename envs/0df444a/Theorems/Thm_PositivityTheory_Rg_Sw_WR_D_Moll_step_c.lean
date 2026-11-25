-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_Moll_step_c
-- name    : PositivityTheory.Rg.Sw.WR.D.Moll.step_c
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:07:14.327053+00:00
-- url     : https://prove2.me/theorems/9ee6b837-238d-5dac-8ddd-7bcc5069cb11
-- title:
--   Moll: step c
-- statement:
--   The Moll construction uses the step c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/StepC.lean#L15-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/StepC.lean#L15-L43

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_MollId
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_StepC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D PositivityTheory.Rg.Sw.WR.D.Moll
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D
variable {n : ℕ} {X : Type} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
set_option maxHeartbeats 1000000

theorem PositivityTheory.Rg.Sw.WR.D.Moll.step_c (ψ : E n → ℂ) (t ε : ℝ) (ht : t ≠ 0) (hε : 0 < ε) (w : E n) :
    ∫ β, ψ β * ((((|t| / (2 * Real.pi)) ^ (n ^ 2) : ℝ) : ℂ) * kr ε t (w - β)) =
      mM ψ (|t| / (2 * Real.sqrt ε)) w := by sorry
