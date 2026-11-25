-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_det_sq_split
-- name    : PositivityTheory.Rg.Sw.SP.det_sq_split
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:51:52.188961+00:00
-- url     : https://prove2.me/theorems/ae2f6c62-b233-4f75-b349-93a0b9226b70
-- title:
--   SP: det sq split
-- statement:
--   The SP construction uses the det sq split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/DetSqSplit.lean#L37-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/DetSqSplit.lean#L37-L45

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

theorem PositivityTheory.Rg.Sw.SP.det_sq_split (s : ℂ) (hs : s = 1 ∨ s = -1) (B : MC n) :
    (1 + Matrix.of B * Matrix.of B).det =
      (1 - (Complex.I * s) • Matrix.of B).det * (1 + (Complex.I * s) • Matrix.of B).det := by sorry
