-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Tf_Loc_twConj_mul_left
-- name    : PositivityTheory.Rg.Tf.Loc.twConj_mul_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:30:55.997802+00:00
-- url     : https://prove2.me/theorems/deafd618-8e9c-42ff-a23b-a977c3ad2ad3
-- title:
--   Loc: tw Conj mul left
-- statement:
--   The Loc construction uses the tw Conj mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/TwistedFactors/IntegralUnitBaseChange/InvTransposeGLInvTransposeGL.lean#L75-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/TwistedFactors/IntegralUnitBaseChange/InvTransposeGLInvTransposeGL.lean#L75-L79

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

theorem PositivityTheory.Rg.Tf.Loc.twConj_mul_left (θ : Monoid.End G) (δ : G) {h : G} (hh : h ∈ twCent θ δ) (g : G) :
    twConj θ (h * g) δ = twConj θ g δ := by sorry
