-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_deltaC_iter_word
-- name    : PositivityTheory.Rg.Sw.WR.K.GB.deltaC_iter_word
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:06:49.748083+00:00
-- url     : https://prove2.me/theorems/c358f036-e934-5c84-bd57-7a7b81ea81ae
-- title:
--   GB: delta C iter word
-- statement:
--   The GB construction uses the delta C iter word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBLink.lean#L189-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBLink.lean#L189-L215

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBLink
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {F G : Mc n → ℂ} {U : Set (Mc n)}

theorem PositivityTheory.Rg.Sw.WR.K.GB.deltaC_iter_word (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) (N : ℕ) :
    Set.EqOn (DeltaC^[N] F) (fun b => ∑ τ : Fin N → Equiv.Perm (Fin n),
      ((∏ j, (Equiv.Perm.sign (τ j) : ℤ) : ℤ) : ℂ) *
        word ((List.finRange N).flatMap fun j => blk (τ j)) F b) U := by sorry
