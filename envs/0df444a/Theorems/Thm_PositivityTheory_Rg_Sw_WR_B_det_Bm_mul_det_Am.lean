-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_det_Bm_mul_det_Am
-- name    : PositivityTheory.Rg.Sw.WR.B.det_Bm_mul_det_Am
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:26:03.036783+00:00
-- url     : https://prove2.me/theorems/dc40cb09-29e2-4fa7-87aa-779ff05c5f8a
-- title:
--   B: det Bm mul det Am
-- statement:
--   The B construction uses the det Bm mul det Am property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBoundA.lean#L77-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBoundA.lean#L77-L79

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

theorem PositivityTheory.Rg.Sw.WR.B.det_Bm_mul_det_Am {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) :
    (Bm s y).det * (Am s y).det = ((dP y : ℝ) : ℂ) := by sorry
