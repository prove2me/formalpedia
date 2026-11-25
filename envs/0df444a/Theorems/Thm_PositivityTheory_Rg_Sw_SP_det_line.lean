-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_det_line
-- name    : PositivityTheory.Rg.Sw.SP.det_line
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:49:55.294105+00:00
-- url     : https://prove2.me/theorems/d1be4f36-3b04-4d80-8715-aeca8b0d7261
-- title:
--   SP: det line
-- statement:
--   The SP construction uses the det line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/DetSqSplit.lean#L14-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/DetSqSplit.lean#L14-L32

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeH
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_DetSqSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
open PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.SP.det_line (M0 A : Matrix (Fin n) (Fin n) ℂ) (h : M0.det ≠ 0) :
    HasDerivAt (fun t : ℂ => (M0 + t • A).det) (M0.det * (M0⁻¹ * A).trace) 0 := by sorry
