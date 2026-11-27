-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Tf_Loc_quotLIntegral_eq
-- name    : PositivityTheory.Rg.Tf.Loc.quotLIntegral_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:53:26.162941+00:00
-- url     : https://prove2.me/theorems/e6c31c89-1346-4dd8-ae23-30f1d9042624
-- title:
--   Loc: quot LIntegral eq
-- statement:
--   The Loc construction uses the quot LIntegral eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/TwistedFactors/IntegralUnitBaseChange/InvTransposeGLInvTransposeGL.lean#L148-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/TwistedFactors/IntegralUnitBaseChange/InvTransposeGLInvTransposeGL.lean#L148-L156

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_InvTransposeGLInvTransposeGL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Polynomial
open scoped ENNReal
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Tf PositivityTheory.Rg.Tf.Loc
noncomputable section
variable {G : Type*} [Group G]
variable [MeasurableSpace G]

theorem PositivityTheory.Rg.Tf.Loc.quotLIntegral_eq [MeasurableMul₂ G] [MeasurableInv G]
    {μG : Measure G} [μG.IsMulLeftInvariant] [SFinite μG]
    {H : Subgroup G} {μH : Measure H} [SFinite μH] [μH.IsInvInvariant]
    {F : G → ℝ≥0∞} (hF : Measurable F) (hFH : ∀ h ∈ H, ∀ g, F (h * g) = F g)
    {ρ : G → ℝ≥0∞} (hρ : IsQuotNormaliser H μH ρ) :
    quotLIntegral μG H μH F = ∫⁻ g, F g * ρ g ∂μG := by sorry
