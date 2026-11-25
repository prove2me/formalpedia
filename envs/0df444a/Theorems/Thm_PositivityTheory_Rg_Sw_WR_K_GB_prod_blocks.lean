-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_prod_blocks
-- name    : PositivityTheory.Rg.Sw.WR.K.GB.prod_blocks
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:50:17.980209+00:00
-- url     : https://prove2.me/theorems/51c55adf-55ca-4baa-905e-d01b04b80fc8
-- title:
--   GB: prod blocks
-- statement:
--   The GB construction uses the prod blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBFinal.lean#L150-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBFinal.lean#L150-L153

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

theorem PositivityTheory.Rg.Sw.WR.K.GB.prod_blocks (N : ℕ) (g : Fin N → Fin n → ℝ) :
    ((List.finRange N).flatMap fun j => (List.finRange n).map fun k => g j k).prod = ∏ j, ∏ k, g j k := by sorry
