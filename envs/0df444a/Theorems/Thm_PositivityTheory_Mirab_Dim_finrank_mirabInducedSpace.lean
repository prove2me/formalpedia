-- Prove2me | Theorems.Thm_PositivityTheory_Mirab_Dim_finrank_mirabInducedSpace
-- name    : PositivityTheory.Mirab.Dim.finrank_mirabInducedSpace
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T18:13:03.827689+00:00
-- url     : https://prove2.me/theorems/019c3647-9d28-5663-bfed-e18e592bf6aa
-- title:
--   Dim: finrank mirab Induced Space
-- statement:
--   The Dim construction uses the finrank mirab Induced Space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/RegularisedThetaMirabolic/CuspidalMirabolic/IndDim.lean#L99-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/RegularisedThetaMirabolic/CuspidalMirabolic/IndDim.lean#L99-L101

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_BlockTriangularOfSubOne
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_Development_WeilBound_CoreStatements_RegularisedThetaMirabolic_CuspidalMirabolic_IndDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.FiniteGL Formalism.L2.Indef.Tree Formalism.EigenvalueLevelCeiling
open PositivityTheory PositivityTheory.Mirab PositivityTheory.Mirab.Dim
variable {k : Type} [Field k] [Fintype k] (n : ℕ)
variable (ψ₀ : AddChar k ℂ)

theorem PositivityTheory.Mirab.Dim.finrank_mirabInducedSpace (ψ₀ : AddChar k ℂ) :
    Module.finrank ℂ (MirabInducedSpace n ψ₀) = ∏ i ∈ Finset.Ico 1 (n + 1), (Fintype.card k ^ i - 1) := by sorry
