-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Tf_Loc_thetaGL_apply
-- name    : PositivityTheory.Rg.Tf.Loc.thetaGL_apply
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:34:56.156954+00:00
-- url     : https://prove2.me/theorems/515cadcf-d91c-43d6-b943-c59990ed4e3b
-- title:
--   Loc: theta GL apply
-- statement:
--   The Loc construction uses the theta GL apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/TwistedFactors/IntegralUnitBaseChange/InvTransposeGLInvTransposeGL.lean#L307-L308
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/TwistedFactors/IntegralUnitBaseChange/InvTransposeGLInvTransposeGL.lean#L307-L308

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

theorem PositivityTheory.Rg.Tf.Loc.thetaGL_apply (σ : E ≃ₐ[k] E) (J g : GL n E) :
    thetaGL σ J g = J * invTransposeGL (sigmaGL σ g) * J⁻¹ := by sorry
