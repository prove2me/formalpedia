-- Prove2me | Theorems.Thm_PositivityTheory_Mirab_Dim_cls_mul
-- name    : PositivityTheory.Mirab.Dim.cls_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T18:23:42.313906+00:00
-- url     : https://prove2.me/theorems/991c43ab-cb6c-45d5-bcfb-86d5e6c42f72
-- title:
--   Dim: cls mul
-- statement:
--   The Dim construction uses the cls mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/RegularisedThetaMirabolic/CuspidalMirabolic/IndDim.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/RegularisedThetaMirabolic/CuspidalMirabolic/IndDim.lean#L25-L29

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

theorem PositivityTheory.Mirab.Dim.cls_mul (u : uniSub k n) (x : mirabSub k n) : cls n ((u : mirabSub k n) * x) = cls n x := by sorry
