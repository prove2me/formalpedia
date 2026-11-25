-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_Moll_step_a
-- name    : PositivityTheory.Rg.Sw.WR.D.Moll.step_a
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:01:31.129051+00:00
-- url     : https://prove2.me/theorems/a7c2dfda-e18e-453d-af95-d08e5298aff3
-- title:
--   Moll: step a
-- statement:
--   The Moll construction uses the step a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ExpCombine.lean#L23-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ExpCombine.lean#L23-L54

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_MollId
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ExpCombine
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

theorem PositivityTheory.Rg.Sw.WR.D.Moll.step_a (Ψ : X → ℂ) (qq : X → E n) (hΨ : Integrable Ψ μ) (hqq : Measurable qq) (t ε : ℝ) (hε : 0 < ε)
    (β : E n) :
    ∫ y, (∫ x, Ψ x * Complex.exp (Complex.I * t * ip y (qq x)) ∂μ) * gam ε y *
        Complex.exp (-(Complex.I * t * ip β y)) =
      ∫ x, Ψ x * kr ε t (qq x - β) ∂μ := by sorry
