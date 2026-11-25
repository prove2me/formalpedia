-- Prove2me | Theorems.Thm_PositivityTheory_Mirab_Dim_restr_injective
-- name    : PositivityTheory.Mirab.Dim.restr_injective
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T18:13:11.159361+00:00
-- url     : https://prove2.me/theorems/e9f2ade5-7c5c-5388-b5df-2da91d8052e8
-- title:
--   Dim: restr injective
-- statement:
--   The Dim construction uses the restr injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/RegularisedThetaMirabolic/CuspidalMirabolic/IndDim.lean#L74-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/RegularisedThetaMirabolic/CuspidalMirabolic/IndDim.lean#L74-L81

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

theorem PositivityTheory.Mirab.Dim.restr_injective : Function.Injective (restr n ψ₀) := by sorry
