-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_Inv_eq_sum_E
-- name    : PositivityTheory.Rg.Sw.WR.K.GB.Inv.eq_sum_E
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:52:22.9128+00:00
-- url     : https://prove2.me/theorems/b67669be-0d32-5275-bf4a-3117be1f0ef5
-- title:
--   Inv: eq sum E
-- statement:
--   The Inv construction uses the eq sum E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBInvar.lean#L59-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBInvar.lean#L59-L61

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBInvar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open PositivityTheory.Rg.Sw.WR.K.GB.Inv

theorem PositivityTheory.Rg.Sw.WR.K.GB.Inv.eq_sum_E (H : Mc n) : H = ∑ p : Fin n × Fin n, H p.1 p.2 • E p := by sorry
