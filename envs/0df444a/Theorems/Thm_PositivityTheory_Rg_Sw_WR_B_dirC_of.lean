-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_dirC_of
-- name    : PositivityTheory.Rg.Sw.WR.B.dirC_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:26:41.750438+00:00
-- url     : https://prove2.me/theorems/1c25d438-aa08-45c8-bc9e-15ba8c455892
-- title:
--   B: dir C of
-- statement:
--   The B construction uses the dir C of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBoundB.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBoundB.lean#L23-L25

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

theorem PositivityTheory.Rg.Sw.WR.B.dirC_of {f : E n → ℂ} {f' : E n →L[ℝ] ℂ} {y : E n} (h : HasFDerivAt f f' y) (w : Fin n → Fin n → ℂ) :
    dirC f w y = f' (fun a b => (w a b).re) + Complex.I * f' (fun a b => (w a b).im) := by sorry
