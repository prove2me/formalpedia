-- Prove2me | Theorems.Thm_P2M_GlobalTheory_AnValJetEx_res_id__2d4fc12792de
-- name    : P2M_GlobalTheory_AnValJetEx_res_id__2d4fc12792de
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-27T04:58:57.105193+00:00
-- url     : https://prove2.me/theorems/eabe4b1c-0510-50a3-9aae-3874db2242c6
-- title:
--   P2 M Global Theory An Val Jet Ex res id  2d4fc12792de: P2 M Global Theory An Val Jet Ex res id  2d4fc12792de
-- statement:
--   The P2 M Global Theory An Val Jet Ex res id  2d4fc12792de construction uses the P2 M Global Theory An Val Jet Ex res id  2d4fc12792de property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsGeneratorJetReading.lean#L39-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsGeneratorJetReading.lean#L39-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsGeneratorJetReading
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
open GlobalTheory GlobalTheory.AnValJetEx
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory

theorem P2M_GlobalTheory_AnValJetEx_res_id__2d4fc12792de {X : Scheme.{0}} {U : X.Opens} (h : U ≤ U) (a : Γ(X, U)ˣ) : res h a = a := by sorry

alias «GlobalTheory».«AnValJetEx».«res_id'» := P2M_GlobalTheory_AnValJetEx_res_id__2d4fc12792de
