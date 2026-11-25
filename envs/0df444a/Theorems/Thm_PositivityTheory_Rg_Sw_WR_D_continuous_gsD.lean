-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_continuous_gsD
-- name    : PositivityTheory.Rg.Sw.WR.D.continuous_gsD
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:08:13.470854+00:00
-- url     : https://prove2.me/theorems/a8313467-553b-5b4c-9e49-1eb2c4b98dbd
-- title:
--   D: continuous gs D
-- statement:
--   The D construction uses the continuous gs D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/DerivFA.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/DerivFA.lean#L27-L29

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

theorem PositivityTheory.Rg.Sw.WR.D.continuous_gsD (c : ℝ) : Continuous (gs (m := m) (n := n) c) := by sorry
