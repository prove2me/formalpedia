-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_Moll_eq_A
-- name    : PositivityTheory.Rg.Sw.WR.D.Moll.eq_A
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:01:26.388989+00:00
-- url     : https://prove2.me/theorems/d97f62d9-2794-44d4-a2a8-dd2f476ed886
-- title:
--   Moll: eq A
-- statement:
--   The Moll construction uses the eq A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ContinuousCexpIp.lean#L81-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ContinuousCexpIp.lean#L81-L94

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ExpCombine
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_StepB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_StepC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousCexpIp
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

theorem PositivityTheory.Rg.Sw.WR.D.Moll.eq_A (Ψ : X → ℂ) (qq : X → E n) (hΨ : Integrable Ψ μ) (hqq : Measurable qq) (t : ℝ) (ht : t ≠ 0)
    (ψ : E n → ℂ) (hψc : Continuous ψ) (hψi : Integrable ψ) (ε : ℝ) (hε : 0 < ε) :
    ∫ β, ψ β * ((((|t| / (2 * Real.pi)) ^ (n ^ 2) : ℝ) : ℂ) *
        ∫ y, (∫ x, Ψ x * Complex.exp (Complex.I * t * ip y (qq x)) ∂μ) * gam ε y *
          Complex.exp (-(Complex.I * t * ip β y))) =
      ∫ x, Ψ x * mM ψ (|t| / (2 * Real.sqrt ε)) (qq x) ∂μ := by sorry
