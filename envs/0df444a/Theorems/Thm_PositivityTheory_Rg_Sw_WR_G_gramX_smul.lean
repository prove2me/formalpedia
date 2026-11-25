-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_gramX_smul
-- name    : PositivityTheory.Rg.Sw.WR.G.gramX_smul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:08:31.676347+00:00
-- url     : https://prove2.me/theorems/a06c85b8-fc3c-5ca2-a10b-ed87b34eba91
-- title:
--   G: gram X smul
-- statement:
--   The G construction uses the gram X smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ContinuousGramX.lean#L46-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ContinuousGramX.lean#L46-L58

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_NormMono
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousGramX
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.G
open PositivityTheory.Rg.Sw

theorem PositivityTheory.Rg.Sw.WR.G.gramX_smul {m n : ℕ} (ε : Fin m → Bool) (ζ : ℂ) (hζ : ‖ζ‖ = 1) (x : Fin m → Fin n → ℂ) :
    gramX ε (ζ • x) = gramX ε x := by sorry
