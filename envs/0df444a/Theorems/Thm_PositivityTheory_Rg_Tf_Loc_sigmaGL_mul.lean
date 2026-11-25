-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Tf_Loc_sigmaGL_mul
-- name    : PositivityTheory.Rg.Tf.Loc.sigmaGL_mul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:02:45.060225+00:00
-- url     : https://prove2.me/theorems/8afb7021-bc4f-4ce6-a538-531bccde3385
-- title:
--   Loc: sigma GL mul
-- statement:
--   The Loc construction uses the sigma GL mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/TwistedFactors/IntegralUnitBaseChange/InvTransposeGLInvTransposeGL.lean#L179-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/TwistedFactors/IntegralUnitBaseChange/InvTransposeGLInvTransposeGL.lean#L179-L182

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

theorem PositivityTheory.Rg.Tf.Loc.sigmaGL_mul (τ τ' : E ≃ₐ[k] E) :
    (sigmaGL (τ * τ') : Monoid.End (GL n E)) = sigmaGL τ * sigmaGL τ' := by sorry
