-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_det_line
-- name    : PositivityTheory.Rg.Sw.WR.B.det_line
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:50:20.496672+00:00
-- url     : https://prove2.me/theorems/fc4e5fea-0b4a-4260-b08c-e54ccb59a77c
-- title:
--   B: det line
-- statement:
--   The B construction uses the det line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBound.lean#L20-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBound.lean#L20-L41

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.B
open PositivityTheory.Rg.Sw
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.WR.B.det_line (M N : Matrix (Fin n) (Fin n) ℂ) (hM : M.det ≠ 0) :
    HasDerivAt (fun t : ℝ => (M + (t : ℂ) • N).det) (M.det * (M⁻¹ * N).trace) 0 := by sorry
