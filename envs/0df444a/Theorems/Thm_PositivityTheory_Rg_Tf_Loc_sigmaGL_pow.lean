-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Tf_Loc_sigmaGL_pow
-- name    : PositivityTheory.Rg.Tf.Loc.sigmaGL_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:40:42.094285+00:00
-- url     : https://prove2.me/theorems/10e7f66d-baae-4fba-98d6-265463f07c98
-- title:
--   Loc: sigma GL pow
-- statement:
--   The Loc construction uses the sigma GL pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/TwistedFactors/IntegralUnitBaseChange/InvTransposeGLInvTransposeGL.lean#L188-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/TwistedFactors/IntegralUnitBaseChange/InvTransposeGLInvTransposeGL.lean#L188-L192

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

theorem PositivityTheory.Rg.Tf.Loc.sigmaGL_pow (τ : E ≃ₐ[k] E) (m : ℕ) :
    (sigmaGL (τ ^ m) : Monoid.End (GL n E)) = sigmaGL τ ^ m := by sorry
