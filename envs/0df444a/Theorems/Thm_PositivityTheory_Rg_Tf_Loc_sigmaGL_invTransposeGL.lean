-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Tf_Loc_sigmaGL_invTransposeGL
-- name    : PositivityTheory.Rg.Tf.Loc.sigmaGL_invTransposeGL
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:02:39.217319+00:00
-- url     : https://prove2.me/theorems/601241b2-d9ef-43ed-9789-708ae7499ef7
-- title:
--   Loc: sigma GL inv Transpose GL
-- statement:
--   The Loc construction uses the sigma GL inv Transpose GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/TwistedFactors/IntegralUnitBaseChange/InvTransposeGLInvTransposeGL.lean#L432-L438
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/TwistedFactors/IntegralUnitBaseChange/InvTransposeGLInvTransposeGL.lean#L432-L438

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

theorem PositivityTheory.Rg.Tf.Loc.sigmaGL_invTransposeGL (τ : E ≃ₐ[k] E) (g : GL n E) :
    sigmaGL τ (invTransposeGL g) = invTransposeGL (sigmaGL τ g) := by sorry
