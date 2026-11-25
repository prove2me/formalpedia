-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Tf_Loc_coeff_charpoly_normGL_fixed
-- name    : PositivityTheory.Rg.Tf.Loc.coeff_charpoly_normGL_fixed
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:02:20.531005+00:00
-- url     : https://prove2.me/theorems/e839d903-4786-5afa-96a1-d64f009a95f8
-- title:
--   Loc: coeff charpoly norm GL fixed
-- statement:
--   The Loc construction uses the coeff charpoly norm GL fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/TwistedFactors/IntegralUnitBaseChange/InvTransposeGLInvTransposeGL.lean#L209-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/TwistedFactors/IntegralUnitBaseChange/InvTransposeGLInvTransposeGL.lean#L209-L214

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

theorem PositivityTheory.Rg.Tf.Loc.coeff_charpoly_normGL_fixed (σ : E ≃ₐ[k] E) (hℓ : σ ^ Module.finrank k E = 1)
    (δ : GL n E) (i : ℕ) :
    σ (((normGL σ δ : GL n E) : Matrix n n E).charpoly.coeff i) =
      ((normGL σ δ : GL n E) : Matrix n n E).charpoly.coeff i := by sorry
