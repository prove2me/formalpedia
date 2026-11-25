-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HermFrame_conjTranspose_toBlocks___d5df6ab04568
-- name    : P2M_GlobalTheory_HermFrame_conjTranspose_toBlocks___d5df6ab04568
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:06:08.396255+00:00
-- url     : https://prove2.me/theorems/0e163816-a794-41f1-b99b-2d3a8c78657f
-- title:
--   P2 M Global Theory Herm Frame conj Transpose to Blocks   d5df6ab04568: P2 M Global Theory Herm Frame conj Transpose to Blocks   d5df6ab04568
-- statement:
--   The P2 M Global Theory Herm Frame conj Transpose to Blocks   d5df6ab04568 construction uses the P2 M Global Theory Herm Frame conj Transpose to Blocks   d5df6ab04568 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L423-L424
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/LeTwoMulOfForallScale.lean#L423-L424

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate
open scoped ComplexOrder MatrixOrder
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {m n l : Type*} [Fintype m] [Fintype n] [Fintype l]
variable [DecidableEq m] [DecidableEq l]
variable {H : Matrix (m ⊕ l) (m ⊕ l) ℂ}
omit [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]

theorem P2M_GlobalTheory_HermFrame_conjTranspose_toBlocks___d5df6ab04568 (h : H.IsHermitian) : H.toBlocks₁₂ᴴ = H.toBlocks₂₁ := by sorry

alias «GlobalTheory».«HermFrame».«conjTranspose_toBlocks₁₂» := P2M_GlobalTheory_HermFrame_conjTranspose_toBlocks___d5df6ab04568
