-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_HSt_CompactCayleyBlocks_inv_trace
-- name    : PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks.inv_trace
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:53:56.139459+00:00
-- url     : https://prove2.me/theorems/d4233d3a-628d-481e-ae7a-854149ad475a
-- title:
--   Compact Cayley Blocks: inv trace
-- statement:
--   The Compact Cayley Blocks construction uses the inv trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/CayleyCosetSums/SpanUnitaryMatrix.lean#L53-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/CayleyCosetSums/SpanUnitaryMatrix.lean#L53-L112

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

theorem PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks.inv_trace (L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ)
    (h : ∀ U X : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 → Xᴴ * X = 1 → L (U * X * Uᴴ) = L X) :
    ∀ X, L X = L 1 / n * X.trace := by sorry
