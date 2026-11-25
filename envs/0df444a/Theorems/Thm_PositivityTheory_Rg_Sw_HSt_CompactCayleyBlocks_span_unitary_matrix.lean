-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_HSt_CompactCayleyBlocks_span_unitary_matrix
-- name    : PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks.span_unitary_matrix
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:54:46.508962+00:00
-- url     : https://prove2.me/theorems/217441bf-ffe9-5085-939c-27dbb41e2c7b
-- title:
--   Compact Cayley Blocks: span unitary matrix
-- statement:
--   The Compact Cayley Blocks construction uses the span unitary matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/CayleyCosetSums/SpanUnitaryMatrix.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/CayleyCosetSums/SpanUnitaryMatrix.lean#L11-L13

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

theorem PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks.span_unitary_matrix :
    Submodule.span ℂ (unitary (Matrix (Fin n) (Fin n) ℂ) : Set (Matrix (Fin n) (Fin n) ℂ)) = ⊤ := by sorry
