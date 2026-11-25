-- Prove2me | Theorems.Thm_PositivityTheory_Mirab_Dim_restr_surjective
-- name    : PositivityTheory.Mirab.Dim.restr_surjective
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T18:13:14.669856+00:00
-- url     : https://prove2.me/theorems/00f678b9-de27-52a8-9c14-a568dc9e3dad
-- title:
--   Dim: restr surjective
-- statement:
--   The Dim construction uses the restr surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/RegularisedThetaMirabolic/CuspidalMirabolic/IndDim.lean#L83-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/RegularisedThetaMirabolic/CuspidalMirabolic/IndDim.lean#L83-L90

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

theorem PositivityTheory.Mirab.Dim.restr_surjective : Function.Surjective (restr n ψ₀) := by sorry
