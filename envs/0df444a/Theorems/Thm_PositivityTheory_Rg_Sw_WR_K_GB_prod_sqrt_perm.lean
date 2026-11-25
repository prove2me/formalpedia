-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_prod_sqrt_perm
-- name    : PositivityTheory.Rg.Sw.WR.K.GB.prod_sqrt_perm
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:52:38.168464+00:00
-- url     : https://prove2.me/theorems/661282cb-80c7-55ac-9c91-1ec43d597786
-- title:
--   GB: prod sqrt perm
-- statement:
--   The GB construction uses the prod sqrt perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBFinal.lean#L159-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBFinal.lean#L159-L164

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_Lagr
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBFinal
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

theorem PositivityTheory.Rg.Sw.WR.K.GB.prod_sqrt_perm (σ : Equiv.Perm (Fin n)) (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) :
    ∏ k, Real.sqrt (w (σ k) * w k) = ∏ k, w k := by sorry
