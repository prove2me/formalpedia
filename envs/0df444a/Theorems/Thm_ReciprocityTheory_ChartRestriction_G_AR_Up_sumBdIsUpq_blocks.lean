-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBdIsUpq_blocks
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.sumBdIsUpq_blocks
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:35:50.492439+00:00
-- url     : https://prove2.me/theorems/06f0efd8-bf44-43a2-9d7d-b12b6e3867f0
-- title:
--   Up: sum Bd Is Upq blocks
-- statement:
--   The Up construction uses the sum Bd Is Upq blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/SumBoundStatementPfA.lean#L24-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/SumBoundStatementPfA.lean#L24-L44

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPfA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open Matrix Topology Filter
open scoped Matrix ComplexOrder ENNReal
noncomputable section
variable {p q : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.sumBdIsUpq_blocks {M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (h : IsUpq M) :
    M.toBlocks₁₁ᴴ * M.toBlocks₁₁ = 1 + M.toBlocks₂₁ᴴ * M.toBlocks₂₁ ∧
    M.toBlocks₂₂ᴴ * M.toBlocks₂₂ = 1 + M.toBlocks₁₂ᴴ * M.toBlocks₁₂ ∧
    M.toBlocks₁₁ * M.toBlocks₁₁ᴴ = 1 + M.toBlocks₁₂ * M.toBlocks₁₂ᴴ ∧
    M.toBlocks₂₂ * M.toBlocks₂₂ᴴ = 1 + M.toBlocks₂₁ * M.toBlocks₂₁ᴴ := by sorry
