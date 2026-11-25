-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Tf_Loc_map_twNorm_of_pow_eq_one
-- name    : PositivityTheory.Rg.Tf.Loc.map_twNorm_of_pow_eq_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:02:29.902362+00:00
-- url     : https://prove2.me/theorems/164f6c40-e0a2-5bc5-8524-77aa99d97932
-- title:
--   Loc: map tw Norm of pow eq one
-- statement:
--   The Loc construction uses the map tw Norm of pow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/TwistedFactors/IntegralUnitBaseChange/InvTransposeGLInvTransposeGL.lean#L56-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/TwistedFactors/IntegralUnitBaseChange/InvTransposeGLInvTransposeGL.lean#L56-L58

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

theorem PositivityTheory.Rg.Tf.Loc.map_twNorm_of_pow_eq_one (θ : Monoid.End G) {ℓ : ℕ} (hℓ : θ ^ ℓ = 1) (δ : G) :
    θ (twNorm θ ℓ δ) = δ⁻¹ * twNorm θ ℓ δ * δ := by sorry
