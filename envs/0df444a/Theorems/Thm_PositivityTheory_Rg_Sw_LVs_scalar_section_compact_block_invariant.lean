-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_scalar_section_compact_block_invariant
-- name    : PositivityTheory.Rg.Sw.LVs.scalar_section_compact_block_invariant
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:59:35.546997+00:00
-- url     : https://prove2.me/theorems/a01f4ffc-3fd2-41db-87da-93383644c1cc
-- title:
--   LVs: scalar section compact block invariant
-- statement:
--   The LVs construction uses the scalar section compact block invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/ScalarSectionCompactBlockInvariant.lean#L185-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/ScalarSectionCompactBlockInvariant.lean#L185-L220

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulConjTransposeEq
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.LVs.scalar_section_compact_block_invariant (hU : UAct) (j : ℕ) (p q : ℤ) (x : M2 n)
    (P' S' : Matrix (Fin n) (Fin n) ℂ) (hP : ∀ a b, P' a b ≠ 0 → a ∈ blkA j ∧ b ∈ blkB j)
    (hS : ∀ a b, S' a b ≠ 0 → a ∈ blkB j ∧ b ∈ blkA j) : f0 p q (x * mX (1 + P') 0 0 (1 + S')) = f0 p q x := by sorry
