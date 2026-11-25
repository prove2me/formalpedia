-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_norm_Fi
-- name    : PositivityTheory.Rg.Sw.WR.D.norm_Fi
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:06:23.207746+00:00
-- url     : https://prove2.me/theorems/8e7c9548-d40a-5262-8bd0-288dca5d563f
-- title:
--   D: norm Fi
-- statement:
--   The D construction uses the norm Fi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/DerivFA.lean#L102-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/DerivFA.lean#L102-L103

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DensDefs
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DerivFA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
variable {m n : ℕ}
variable (ε : Fin m → Bool) (c t : ℝ)
variable {ε c t}

theorem PositivityTheory.Rg.Sw.WR.D.norm_Fi (P : PX m n) (y : E n) (x : Fin m → Fin n → ℂ) : ‖Fi ε c t P y x‖ = ‖evX P x * gs c x‖ := by sorry
