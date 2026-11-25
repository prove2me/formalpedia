-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_evX_smul_mono
-- name    : PositivityTheory.Rg.Sw.WR.G.evX_smul_mono
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:01:21.084567+00:00
-- url     : https://prove2.me/theorems/7ba3fa84-87ef-491e-b409-fa48d6983403
-- title:
--   G: ev X smul mono
-- statement:
--   The G construction uses the ev X smul mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ContinuousGramX.lean#L30-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ContinuousGramX.lean#L30-L40

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

theorem PositivityTheory.Rg.Sw.WR.G.evX_smul_mono {m n : ℕ} (ζ : ℂ) (d : (Fin m × Fin n × Bool) →₀ ℕ) (hd : ∀ k, k.2.2 = true → d k = 0)
    (x : Fin m → Fin n → ℂ) :
    evX (monomial d 1) (ζ • x) = ζ ^ (d.sum fun _ e => e) * evX (monomial d 1) x := by sorry
