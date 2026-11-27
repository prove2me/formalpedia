-- Prove2me | Theorems.Thm_P2M_GlobalTheory_AdjRead_comp_ad__1f5d75380be3
-- name    : P2M_GlobalTheory_AdjRead_comp_ad__1f5d75380be3
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-27T05:46:54.123999+00:00
-- url     : https://prove2.me/theorems/af398c40-d2d8-45be-8a59-164aeb9b38bd
-- title:
--   P2 M Global Theory Adj Read comp ad  1f5d75380be3: P2 M Global Theory Adj Read comp ad  1f5d75380be3
-- statement:
--   The P2 M Global Theory Adj Read comp ad  1f5d75380be3 construction uses the P2 M Global Theory Adj Read comp ad  1f5d75380be3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsAdjReadingOne.lean#L53-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsAdjReadingOne.lean#L53-L56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGenRosati
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsHolFamPullbackLiftOfCommonBaseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AbelianHolomorphicFrameReadingConstOfFormsCancelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_GeneratorReadingCorrMulInvStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_GeneratorReadingPullbackPeriodRigidStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsAdjReadingOne
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AdjRead
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

theorem P2M_GlobalTheory_AdjRead_comp_ad__1f5d75380be3 {T : Over S} (f f' : A ⟶ A) (x y : T ⟶ A) (k) :
    (lift x y).left ≫ adφ f f' k = Sum.elim (cub ![x, y ≫ f']) (cub ![x ≫ f, y]) k := by sorry

alias «GlobalTheory».«AdjRead».«comp_adφ» := P2M_GlobalTheory_AdjRead_comp_ad__1f5d75380be3
