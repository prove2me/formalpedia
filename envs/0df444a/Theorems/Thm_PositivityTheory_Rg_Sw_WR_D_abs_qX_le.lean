-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_abs_qX_le
-- name    : PositivityTheory.Rg.Sw.WR.D.abs_qX_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:01:27.137653+00:00
-- url     : https://prove2.me/theorems/e9125d1c-4b3d-418a-b834-9ce5c8049af2
-- title:
--   D: abs q X le
-- statement:
--   The D construction uses the abs q X le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/DerivFA.lean#L71-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/DerivFA.lean#L71-L79

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

theorem PositivityTheory.Rg.Sw.WR.D.abs_qX_le (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) (a b : Fin n) :
    |qX ε x a b| ≤ 2 * ‖evX (Qp ε a b) x‖ := by sorry
