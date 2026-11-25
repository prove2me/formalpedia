-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_pb_cdOn_inv
-- name    : PositivityTheory.Rg.Sw.WR.K.GB.pb_cdOn_inv
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:50:18.764409+00:00
-- url     : https://prove2.me/theorems/5f85a606-24f1-471d-a49e-a0d7f20ae46a
-- title:
--   GB: pb cd On inv
-- statement:
--   The GB construction uses the pb cd On inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBBound.lean#L40-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBBound.lean#L40-L45

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBBound
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
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.WR.K.GB.pb_cdOn_inv {f : Mc n → Mc n} (hf : ∀ i j, ContDiff ℂ (⊤ : ℕ∞) (fun b => f b i j)) (s : Set (Mc n))
    (hs : ∀ b ∈ s, (f b).det ≠ 0) (i j : Fin n) : ContDiffOn ℂ (⊤ : ℕ∞) (fun b => (f b)⁻¹ i j) s := by sorry
