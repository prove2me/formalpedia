-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_HSt_CompactCayleyBlocks_pm_conj
-- name    : PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks.pm_conj
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:54:56.763484+00:00
-- url     : https://prove2.me/theorems/a5c127b2-04e3-454c-9aa2-539d9a45c6c4
-- title:
--   Compact Cayley Blocks: pm conj
-- statement:
--   The Compact Cayley Blocks construction uses the pm conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/CayleyCosetSums/SpanUnitaryMatrix.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/CayleyCosetSums/SpanUnitaryMatrix.lean#L20-L23

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

theorem PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks.pm_conj (σ : Equiv.Perm (Fin n)) (X : Matrix (Fin n) (Fin n) ℂ) :
    pm σ * X * (pm σ)ᴴ = X.submatrix σ σ := by sorry
