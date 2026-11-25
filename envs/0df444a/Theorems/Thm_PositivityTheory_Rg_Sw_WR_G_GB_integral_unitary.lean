-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GB_integral_unitary
-- name    : PositivityTheory.Rg.Sw.WR.G.GB.integral_unitary
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:01:36.841681+00:00
-- url     : https://prove2.me/theorems/ece873c5-897a-4fcc-b0fe-ddbaf38459fb
-- title:
--   GB: integral unitary
-- statement:
--   The GB construction uses the integral unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBaseB.lean#L20-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBaseB.lean#L20-L48

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBaseA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBaseB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.G PositivityTheory.Rg.Sw.WR.G.GB
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.WR.G.GB.integral_unitary (U : Matrix (Fin n) (Fin n) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (g : (Fin n → ℂ) → ℂ) : ∫ r, g (U *ᵥ r) = ∫ r, g r := by sorry
