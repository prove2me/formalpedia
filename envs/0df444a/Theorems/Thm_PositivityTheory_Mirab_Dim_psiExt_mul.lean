-- Prove2me | Theorems.Thm_PositivityTheory_Mirab_Dim_psiExt_mul
-- name    : PositivityTheory.Mirab.Dim.psiExt_mul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T18:20:59.801917+00:00
-- url     : https://prove2.me/theorems/bd2ded00-9c3c-4d1b-803b-3d9fc4d5e9a2
-- title:
--   Dim: psi Ext mul
-- statement:
--   The Dim construction uses the psi Ext mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/RegularisedThetaMirabolic/CuspidalMirabolic/IndDim.lean#L42-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/RegularisedThetaMirabolic/CuspidalMirabolic/IndDim.lean#L42-L46

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

theorem PositivityTheory.Mirab.Dim.psiExt_mul (u : uniSub k n) (y : mirabSub k n) (hy : y ∈ uniSub k n) :
    psiExt n ψ₀ ((u : mirabSub k n) * y) = genericChar n ψ₀ u * psiExt n ψ₀ y := by sorry
