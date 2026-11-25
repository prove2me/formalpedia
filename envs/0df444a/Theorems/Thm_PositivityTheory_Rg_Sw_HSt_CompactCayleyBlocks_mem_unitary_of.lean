-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_HSt_CompactCayleyBlocks_mem_unitary_of
-- name    : PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks.mem_unitary_of
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:53:01.64766+00:00
-- url     : https://prove2.me/theorems/054cb896-abf7-4f43-aa50-88bd6524af60
-- title:
--   Compact Cayley Blocks: mem unitary of
-- statement:
--   The Compact Cayley Blocks construction uses the mem unitary of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/CayleyCosetSums/SpanUnitaryMatrix.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/CayleyCosetSums/SpanUnitaryMatrix.lean#L15-L16

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_CayleyCosetSums_SpanUnitaryMatrix
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks.mem_unitary_of {U : Matrix (Fin n) (Fin n) ℂ} (h : Uᴴ * U = 1) : U ∈ unitary (Matrix (Fin n) (Fin n) ℂ) := by sorry
