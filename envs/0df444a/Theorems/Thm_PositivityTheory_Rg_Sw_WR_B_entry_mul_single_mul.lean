-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_entry_mul_single_mul
-- name    : PositivityTheory.Rg.Sw.WR.B.entry_mul_single_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:49:37.529795+00:00
-- url     : https://prove2.me/theorems/8f5e3b78-0d9d-4009-b8a1-1fe51887a736
-- title:
--   B: entry mul single mul
-- statement:
--   The B construction uses the entry mul single mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBoundB.lean#L129-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBoundB.lean#L129-L132

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

theorem PositivityTheory.Rg.Sw.WR.B.entry_mul_single_mul (M : Matrix (Fin n) (Fin n) ℂ) (a b k l : Fin n) :
    (M * Matrix.single l k (1 : ℂ) * M) a b = M a l * M k b := by sorry
