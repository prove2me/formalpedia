-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_trace_mul_single
-- name    : PositivityTheory.Rg.Sw.WR.B.trace_mul_single
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:00:41.086917+00:00
-- url     : https://prove2.me/theorems/64b80d88-dd59-4222-aeeb-c4bb420a836d
-- title:
--   B: trace mul single
-- statement:
--   The B construction uses the trace mul single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBoundB.lean#L111-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBoundB.lean#L111-L119

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.B
open PositivityTheory.Rg.Sw
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.WR.B.trace_mul_single (M : Matrix (Fin n) (Fin n) ℂ) (k l : Fin n) : (M * Matrix.single l k (1 : ℂ)).trace = M k l := by sorry
