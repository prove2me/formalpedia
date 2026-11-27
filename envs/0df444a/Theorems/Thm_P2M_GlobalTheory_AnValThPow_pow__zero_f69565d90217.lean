-- Prove2me | Theorems.Thm_P2M_GlobalTheory_AnValThPow_pow__zero_f69565d90217
-- name    : P2M_GlobalTheory_AnValThPow_pow__zero_f69565d90217
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-27T04:57:31.735794+00:00
-- url     : https://prove2.me/theorems/4db3493d-59fb-583b-80ae-6c45495899bd
-- title:
--   P2 M Global Theory An Val Th Pow pow  zero f69565d90217: P2 M Global Theory An Val Th Pow pow  zero f69565d90217
-- statement:
--   The P2 M Global Theory An Val Th Pow pow  zero f69565d90217 construction uses the P2 M Global Theory An Val Th Pow pow  zero f69565d90217 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ThetaConstantPowEqOneOfPowerTrivial.lean#L65-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ThetaConstantPowEqOneOfPowerTrivial.lean#L65-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_GeneratorReadingCorrMulInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ThetaConstantPowEqOneOfPowerTrivial
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
open GlobalTheory GlobalTheory.AnValThPow
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {T : Over S}

theorem P2M_GlobalTheory_AnValThPow_pow__zero_f69565d90217 (x : T ⟶ A) (n : ℕ) (i : Fin n) : powφ A x n (i, 0) = (translPt A (x ^ (i : ℕ))).left := by sorry

alias «GlobalTheory».«AnValThPow».«powφ_zero» := P2M_GlobalTheory_AnValThPow_pow__zero_f69565d90217
