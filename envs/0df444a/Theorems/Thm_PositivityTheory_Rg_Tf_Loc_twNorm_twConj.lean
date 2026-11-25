-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Tf_Loc_twNorm_twConj
-- name    : PositivityTheory.Rg.Tf.Loc.twNorm_twConj
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:02:35.762563+00:00
-- url     : https://prove2.me/theorems/c3e28bcf-1ba2-5005-92d4-e784a98cfc4c
-- title:
--   Loc: tw Norm tw Conj
-- statement:
--   The Loc construction uses the tw Norm tw Conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/TwistedFactors/IntegralUnitBaseChange/InvTransposeGLInvTransposeGL.lean#L36-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/TwistedFactors/IntegralUnitBaseChange/InvTransposeGLInvTransposeGL.lean#L36-L42

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

theorem PositivityTheory.Rg.Tf.Loc.twNorm_twConj (θ : Monoid.End G) (m : ℕ) (g δ : G) :
    twNorm θ m (twConj θ g δ) = g⁻¹ * twNorm θ m δ * (θ ^ m) g := by sorry
