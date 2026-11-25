-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_decay
-- name    : PositivityTheory.Rg.Sw.WR.D.decay
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:01:46.066406+00:00
-- url     : https://prove2.me/theorems/82378ca2-334f-4b87-8c19-d416b9139043
-- title:
--   D: decay
-- statement:
--   The D construction uses the decay property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ContinuousEvXI.lean#L77-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ContinuousEvXI.lean#L77-L109

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DensDefs
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsBisMore
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousEvXI
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D
open PositivityTheory.Rg.Sw
variable {m n : ℕ}

theorem PositivityTheory.Rg.Sw.WR.D.decay (c : ℝ) (hc : 0 < c) (k : ℕ) : ∃ K : ℝ, ∀ s : ℝ, 0 ≤ s → (1 + s) ^ (2 * k) * Real.exp (-(c * s ^ 2)) ≤ K := by sorry
