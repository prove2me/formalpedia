-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Tf_Loc_lintegral_normaliser_eq
-- name    : PositivityTheory.Rg.Tf.Loc.lintegral_normaliser_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:20:59.963614+00:00
-- url     : https://prove2.me/theorems/71d93370-a818-41af-8e5e-5909b4fb07c7
-- title:
--   Loc: lintegral normaliser eq
-- statement:
--   The Loc construction uses the lintegral normaliser eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/TwistedFactors/IntegralUnitBaseChange/InvTransposeGLInvTransposeGL.lean#L113-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/TwistedFactors/IntegralUnitBaseChange/InvTransposeGLInvTransposeGL.lean#L113-L146

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

theorem PositivityTheory.Rg.Tf.Loc.lintegral_normaliser_eq [MeasurableMul₂ G] [MeasurableInv G]
    {μG : Measure G} [μG.IsMulLeftInvariant] [SFinite μG]
    {H : Subgroup G} {μH : Measure H} [SFinite μH] [μH.IsInvInvariant]
    {F : G → ℝ≥0∞} (hF : Measurable F) (hFH : ∀ h ∈ H, ∀ g, F (h * g) = F g)
    {ρ ρ' : G → ℝ≥0∞} (hρ : IsQuotNormaliser H μH ρ) (hρ' : IsQuotNormaliser H μH ρ') :
    ∫⁻ g, F g * ρ g ∂μG = ∫⁻ g, F g * ρ' g ∂μG := by sorry
