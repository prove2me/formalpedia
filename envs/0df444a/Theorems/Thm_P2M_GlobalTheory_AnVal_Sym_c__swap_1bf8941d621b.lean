-- Prove2me | Theorems.Thm_P2M_GlobalTheory_AnVal_Sym_c__swap_1bf8941d621b
-- name    : P2M_GlobalTheory_AnVal_Sym_c__swap_1bf8941d621b
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-27T05:10:52.48238+00:00
-- url     : https://prove2.me/theorems/ba3d3353-5f94-5451-913d-b1393fac3642
-- title:
--   P2 M Global Theory An Val Sym c  swap 1bf8941d621b: P2 M Global Theory An Val Sym c  swap 1bf8941d621b
-- statement:
--   The P2 M Global Theory An Val Sym c  swap 1bf8941d621b construction uses the P2 M Global Theory An Val Sym c  swap 1bf8941d621b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/AnalyticFrameSymmetryTrivial.lean#L67-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/AnalyticFrameSymmetryTrivial.lean#L67-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CorrOfJetsOfAnalyticFrameProductsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_JetReadingLinearSubstitutionPointsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AnalyticFrameSymmetryTrivial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AnVal GlobalTheory.AnVal.Sym
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory

theorem P2M_GlobalTheory_AnVal_Sym_c__swap_1bf8941d621b (I : ULift.{0} (Finset (Fin 2))) : cε 2 (swapI I) = cε 2 I := by sorry

alias «GlobalTheory».«AnVal».«Sym».«cε_swap» := P2M_GlobalTheory_AnVal_Sym_c__swap_1bf8941d621b
