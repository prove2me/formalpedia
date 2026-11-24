-- Prove2me | Theorems.Thm_P2M_GlobalTheory_GermExist_unit_comp_prim__a51190ddb949
-- name    : P2M_GlobalTheory_GermExist_unit_comp_prim__a51190ddb949
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:25:19.248827+00:00
-- url     : https://prove2.me/theorems/3cee8bf3-de35-49fe-8db1-9aef5e338e8e
-- title:
--   P2 M Global Theory Germ Exist unit comp prim  a51190ddb949: P2 M Global Theory Germ Exist unit comp prim  a51190ddb949
-- statement:
--   The P2 M Global Theory Germ Exist unit comp prim  a51190ddb949 construction uses the P2 M Global Theory Germ Exist unit comp prim  a51190ddb949 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/TopLePreimageWchart.lean#L37-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/TopLePreimageWchart.lean#L37-L52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_TopLePreimageWchart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.TB GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.GermExist

theorem P2M_GlobalTheory_GermExist_unit_comp_prim__a51190ddb949 {S : Scheme.{0}} {A : Over S} [GrpObj A] (w : A ⟶ A) (hw : η[A] ≫ w = η[A])
    (k : Fin 5) : η[A].left ≫ primφ w k = η[A].left := by sorry

alias «GlobalTheory».«GermExist».«unit_comp_primφ» := P2M_GlobalTheory_GermExist_unit_comp_prim__a51190ddb949
