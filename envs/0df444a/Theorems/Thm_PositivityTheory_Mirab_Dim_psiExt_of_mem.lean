-- Prove2me | Theorems.Thm_PositivityTheory_Mirab_Dim_psiExt_of_mem
-- name    : PositivityTheory.Mirab.Dim.psiExt_of_mem
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T18:25:41.982116+00:00
-- url     : https://prove2.me/theorems/4d7f7486-ca6c-4b49-ab1d-2a8f924d4b3f
-- title:
--   Dim: psi Ext of mem
-- statement:
--   The Dim construction uses the psi Ext of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/RegularisedThetaMirabolic/CuspidalMirabolic/IndDim.lean#L38-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/RegularisedThetaMirabolic/CuspidalMirabolic/IndDim.lean#L38-L40

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

theorem PositivityTheory.Mirab.Dim.psiExt_of_mem (u : uniSub k n) : psiExt n ψ₀ (u : mirabSub k n) = genericChar n ψ₀ u := by sorry
