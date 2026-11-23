-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_norm_Fd_le
-- name    : PositivityTheory.Rg.Sw.WR.D.norm_Fd_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:50:42.468815+00:00
-- url     : https://prove2.me/theorems/c02fe2d2-bcb6-4902-aaf4-cc3423c03ea5
-- title:
--   D: norm Fd le
-- statement:
--   The D construction uses the norm Fd le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/DerivFA.lean#L119-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/DerivFA.lean#L119-L138

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

theorem PositivityTheory.Rg.Sw.WR.D.norm_Fd_le (P : PX m n) (y : E n) (x : Fin m → Fin n → ℂ) : ‖Fd ε c t P y x‖ ≤ bnd ε c t P x := by sorry
