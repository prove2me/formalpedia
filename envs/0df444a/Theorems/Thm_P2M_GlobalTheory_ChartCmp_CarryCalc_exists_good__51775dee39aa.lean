-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ChartCmp_CarryCalc_exists_good__51775dee39aa
-- name    : P2M_GlobalTheory_ChartCmp_CarryCalc_exists_good__51775dee39aa
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:37:47.317089+00:00
-- url     : https://prove2.me/theorems/bee09222-93d9-47d3-afec-1605d4797343
-- title:
--   P2 M Global Theory Chart Cmp Carry Calc exists good  51775dee39aa: P2 M Global Theory Chart Cmp Carry Calc exists good  51775dee39aa
-- statement:
--   The P2 M Global Theory Chart Cmp Carry Calc exists good  51775dee39aa construction uses the P2 M Global Theory Chart Cmp Carry Calc exists good  51775dee39aa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/CarriesLinCombGeneratorCalculus.lean#L61-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/CarriesLinCombGeneratorCalculus.lean#L61-L63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CarriesLinCombGeneratorCalculus
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.CarryCalc
variable {X X' Y : Scheme.{0}} {L' : LB X'} {L : LB X} {F : X' ⟶ X} {K : Type} [Fintype K]

theorem P2M_GlobalTheory_ChartCmp_CarryCalc_exists_good__51775dee39aa {M : LB X} (hM : M.IsLB) {Z : Scheme.{0}} (z : Z) : ∃ J, Good M z J := by sorry

alias «GlobalTheory».«ChartCmp».«CarryCalc».«exists_good'» := P2M_GlobalTheory_ChartCmp_CarryCalc_exists_good__51775dee39aa
