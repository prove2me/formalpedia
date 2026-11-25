-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_dirC_eval
-- name    : PositivityTheory.Rg.Sw.WR.B.dirC_eval
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:02:46.482155+00:00
-- url     : https://prove2.me/theorems/42ae0a18-c5db-58fb-b34f-8c6b940f2b03
-- title:
--   B: dir C eval
-- statement:
--   The B construction uses the dir C eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBoundB.lean#L55-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBoundB.lean#L55-L84

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.B
open PositivityTheory.Rg.Sw
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.WR.B.dirC_eval {ι : Type} [Fintype ι] [DecidableEq ι] (φ : ι → E n → ℂ) (hφ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (φ i))
    (w : Fin n → Fin n → ℂ) (y : E n) (R : MvPolynomial ι ℂ) :
    dirC (fun y => MvPolynomial.eval (fun i => φ i y) R) w y =
      ∑ i, MvPolynomial.eval (fun i => φ i y) (MvPolynomial.pderiv i R) * dirC (φ i) w y := by sorry
