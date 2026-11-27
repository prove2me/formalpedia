-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Tf_Loc_sigmaGL_val
-- name    : PositivityTheory.Rg.Tf.Loc.sigmaGL_val
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:53:12.437229+00:00
-- url     : https://prove2.me/theorems/91a4426d-91fe-5028-844d-ecb5dfeb6de6
-- title:
--   Loc: sigma GL val
-- statement:
--   The Loc construction uses the sigma GL val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/TwistedFactors/IntegralUnitBaseChange/InvTransposeGLInvTransposeGL.lean#L176-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/TwistedFactors/IntegralUnitBaseChange/InvTransposeGLInvTransposeGL.lean#L176-L177

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

theorem PositivityTheory.Rg.Tf.Loc.sigmaGL_val (τ : E ≃ₐ[k] E) (g : GL n E) :
    ((sigmaGL τ g : GL n E) : Matrix n n E) = (g : Matrix n n E).map τ := by sorry
