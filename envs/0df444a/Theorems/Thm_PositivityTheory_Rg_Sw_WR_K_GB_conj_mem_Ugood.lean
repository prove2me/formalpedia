-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_conj_mem_Ugood
-- name    : PositivityTheory.Rg.Sw.WR.K.GB.conj_mem_Ugood
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:02:50.607107+00:00
-- url     : https://prove2.me/theorems/672b2abb-d2e1-4499-a229-fa4638dd8c8d
-- title:
--   GB: conj mem Ugood
-- statement:
--   The GB construction uses the conj mem Ugood property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBFinal.lean#L166-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBFinal.lean#L166-L170

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

theorem PositivityTheory.Rg.Sw.WR.K.GB.conj_mem_Ugood (s : ℂ) (k : Mc n) (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (b : Mc n) (hb : b ∈ Ugood s) :
    k * b * kᴴ ∈ Ugood s := by sorry
