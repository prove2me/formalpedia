-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Tf_Loc_theta1_sq
-- name    : PositivityTheory.Rg.Tf.Loc.theta1_sq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:53:37.407464+00:00
-- url     : https://prove2.me/theorems/6905ac44-3c29-4e5d-a2ea-8742fe9f0ebb
-- title:
--   Loc: theta1 sq
-- statement:
--   The Loc construction uses the theta1 sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/TwistedFactors/IntegralUnitBaseChange/InvTransposeGLInvTransposeGL.lean#L444-L457
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/TwistedFactors/IntegralUnitBaseChange/InvTransposeGLInvTransposeGL.lean#L444-L457

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
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {k E : Type*} [Field k] [Field E] [Algebra k E]

theorem PositivityTheory.Rg.Tf.Loc.theta1_sq (σ : E ≃ₐ[k] E) (hσ : σ ^ 2 = 1) :
    (theta1 σ : Monoid.End (GL n E)) ^ 2 = 1 := by sorry
