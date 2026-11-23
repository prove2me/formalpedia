-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Tf_Loc_twCent_commute_twNorm
-- name    : PositivityTheory.Rg.Tf.Loc.twCent_commute_twNorm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:32:35.836022+00:00
-- url     : https://prove2.me/theorems/ae86d34b-cdaa-4fb8-bd96-37fecbb8fd14
-- title:
--   Loc: tw Cent commute tw Norm
-- statement:
--   The Loc construction uses the tw Cent commute tw Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/TwistedFactors/IntegralUnitBaseChange/InvTransposeGLInvTransposeGL.lean#L81-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/TwistedFactors/IntegralUnitBaseChange/InvTransposeGLInvTransposeGL.lean#L81-L87

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

theorem PositivityTheory.Rg.Tf.Loc.twCent_commute_twNorm (θ : Monoid.End G) {ℓ : ℕ} (hℓ : θ ^ ℓ = 1) (δ : G) {g : G}
    (hg : g ∈ twCent θ δ) : g * twNorm θ ℓ δ = twNorm θ ℓ δ * g := by sorry
