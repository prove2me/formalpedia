-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Tf_Loc_map_twNorm
-- name    : PositivityTheory.Rg.Tf.Loc.map_twNorm
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:02:31.184507+00:00
-- url     : https://prove2.me/theorems/205e0046-30cf-50e6-aea9-40bd22deb3c8
-- title:
--   Loc: map tw Norm
-- statement:
--   The Loc construction uses the map tw Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/TwistedFactors/IntegralUnitBaseChange/InvTransposeGLInvTransposeGL.lean#L48-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/TwistedFactors/IntegralUnitBaseChange/InvTransposeGLInvTransposeGL.lean#L48-L54

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

theorem PositivityTheory.Rg.Tf.Loc.map_twNorm (θ : Monoid.End G) (m : ℕ) (δ : G) :
    θ (twNorm θ m δ) = δ⁻¹ * twNorm θ m δ * (θ ^ m) δ := by sorry
