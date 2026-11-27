-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Tf_Loc_charpoly_normGL_lifts
-- name    : PositivityTheory.Rg.Tf.Loc.charpoly_normGL_lifts
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:54:06.149244+00:00
-- url     : https://prove2.me/theorems/3c1a25c9-6609-4e01-afd2-78eb9b0218a2
-- title:
--   Loc: charpoly norm GL lifts
-- statement:
--   The Loc construction uses the charpoly norm GL lifts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/TwistedFactors/IntegralUnitBaseChange/InvTransposeGLInvTransposeGL.lean#L216-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/TwistedFactors/IntegralUnitBaseChange/InvTransposeGLInvTransposeGL.lean#L216-L234

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

theorem PositivityTheory.Rg.Tf.Loc.charpoly_normGL_lifts [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E)
    (hgen : ∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) (δ : GL n E) :
    ∃ P : k[X], P.map (algebraMap k E) = ((normGL σ δ : GL n E) : Matrix n n E).charpoly := by sorry
