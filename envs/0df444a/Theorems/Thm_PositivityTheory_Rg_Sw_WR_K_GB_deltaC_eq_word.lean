-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_deltaC_eq_word
-- name    : PositivityTheory.Rg.Sw.WR.K.GB.deltaC_eq_word
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:02:56.155103+00:00
-- url     : https://prove2.me/theorems/d541fc80-8498-46a9-a242-e2a71a91f00c
-- title:
--   GB: delta C eq word
-- statement:
--   The GB construction uses the delta C eq word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBLink.lean#L179-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBLink.lean#L179-L182

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

theorem PositivityTheory.Rg.Sw.WR.K.GB.deltaC_eq_word (H : Mc n → ℂ) :
    DeltaC H = fun b => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * word (blk σ) H b := by sorry
