-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Tf_Loc_charpoly_twNorm_map
-- name    : PositivityTheory.Rg.Tf.Loc.charpoly_twNorm_map
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:02:37.290979+00:00
-- url     : https://prove2.me/theorems/e46677e5-8993-4a33-a383-6fe1230a1a65
-- title:
--   Loc: charpoly tw Norm map
-- statement:
--   The Loc construction uses the charpoly tw Norm map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/TwistedFactors/IntegralUnitBaseChange/InvTransposeGLInvTransposeGL.lean#L199-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/TwistedFactors/IntegralUnitBaseChange/InvTransposeGLInvTransposeGL.lean#L199-L207

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

theorem PositivityTheory.Rg.Tf.Loc.charpoly_twNorm_map (σ : E ≃ₐ[k] E) {ℓ : ℕ} (hℓ : σ ^ ℓ = 1) (δ : GL n E) :
    ((twNorm (sigmaGL σ) ℓ δ : GL n E) : Matrix n n E).charpoly.map (σ.toAlgHom.toRingHom) =
      ((twNorm (sigmaGL σ) ℓ δ : GL n E) : Matrix n n E).charpoly := by sorry
