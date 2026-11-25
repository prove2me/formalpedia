-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_norm_det_pow
-- name    : PositivityTheory.Rg.Sw.WR.B.norm_det_pow
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:06:25.323702+00:00
-- url     : https://prove2.me/theorems/f39118a1-9563-5fa5-9135-e30f3e577651
-- title:
--   B: norm det pow
-- statement:
--   The B construction uses the norm det pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBoundA.lean#L163-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBoundA.lean#L163-L172

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundA
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
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.B
open PositivityTheory.Rg.Sw
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.WR.B.norm_det_pow {x : ℂ} {d : ℝ} (hd : 0 < d) (h : ‖x‖ ^ 2 = d⁻¹) (p : ℕ) : ‖x ^ p‖ = d ^ (-(p : ℝ) / 2) := by sorry
