-- Prove2me | Theorems.Thm_P2M_GlobalTheory_AnVal_JetCorr_jetOf_pow__0a4f0e599833
-- name    : P2M_GlobalTheory_AnVal_JetCorr_jetOf_pow__0a4f0e599833
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-27T04:49:06.762406+00:00
-- url     : https://prove2.me/theorems/ceeb7a8e-c49e-5406-84b4-0893db29afda
-- title:
--   P2 M Global Theory An Val Jet Corr jet Of pow  0a4f0e599833: P2 M Global Theory An Val Jet Corr jet Of pow  0a4f0e599833
-- statement:
--   The P2 M Global Theory An Val Jet Corr jet Of pow  0a4f0e599833 construction uses the P2 M Global Theory An Val Jet Corr jet Of pow  0a4f0e599833 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CorrOfJetsOfAnalyticFrameProducts.lean#L51-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CorrOfJetsOfAnalyticFrameProducts.lean#L51-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FderivEqOfJetOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CorrOfJetsOfAnalyticFrameProducts
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
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AnVal GlobalTheory.AnVal.JetCorr
variable {N : ℕ} (m : ℕ)

theorem P2M_GlobalTheory_AnVal_JetCorr_jetOf_pow__0a4f0e599833 {F : (Fin N → ℂ) → ℂ} (hF : AnalyticAt ℂ F 0) (k : ℕ) :
    jetOf m (fun v => F v ^ k) = jetOf m F ^ k := by sorry

alias «GlobalTheory».«AnVal».«JetCorr».«jetOf_pow'» := P2M_GlobalTheory_AnVal_JetCorr_jetOf_pow__0a4f0e599833
