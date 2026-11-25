-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_diff_inv_Y
-- name    : PositivityTheory.Rg.Sw.SP.diff_inv_Y
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:50:40.912399+00:00
-- url     : https://prove2.me/theorems/fe547fc8-6ab6-4320-b000-40d2b79ece62
-- title:
--   SP: diff inv Y
-- statement:
--   The SP construction uses the diff inv Y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/BridgeH.lean#L88-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/BridgeH.lean#L88-L99

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeH
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

theorem PositivityTheory.Rg.Sw.SP.diff_inv_Y (s : ℂ) (x v : MC n) (h : (1 + (Complex.I * s) • Matrix.of x).det ≠ 0) (a d : Fin n) :
    DifferentiableAt ℂ (fun t : ℂ => ((1 + (Complex.I * s) • Matrix.of x) + t • ((Complex.I * s) • Matrix.of v))⁻¹ a d) 0 := by sorry
