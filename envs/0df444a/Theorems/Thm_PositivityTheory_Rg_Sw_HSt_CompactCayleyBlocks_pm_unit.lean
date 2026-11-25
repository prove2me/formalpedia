-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_HSt_CompactCayleyBlocks_pm_unit
-- name    : PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks.pm_unit
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:54:59.581427+00:00
-- url     : https://prove2.me/theorems/555929db-072a-4ba9-b229-8975dafc82bb
-- title:
--   Compact Cayley Blocks: pm unit
-- statement:
--   The Compact Cayley Blocks construction uses the pm unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/CayleyCosetSums/SpanUnitaryMatrix.lean#L25-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/CayleyCosetSums/SpanUnitaryMatrix.lean#L25-L33

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

theorem PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks.pm_unit (σ : Equiv.Perm (Fin n)) : (pm σ)ᴴ * pm σ = 1 := by sorry
