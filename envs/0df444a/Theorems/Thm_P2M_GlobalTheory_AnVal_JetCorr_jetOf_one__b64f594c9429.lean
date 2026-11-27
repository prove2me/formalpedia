-- Prove2me | Theorems.Thm_P2M_GlobalTheory_AnVal_JetCorr_jetOf_one__b64f594c9429
-- name    : P2M_GlobalTheory_AnVal_JetCorr_jetOf_one__b64f594c9429
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-27T04:48:32.105802+00:00
-- url     : https://prove2.me/theorems/4a8deb9e-5524-58cf-b1de-a3f698e705fb
-- title:
--   P2 M Global Theory An Val Jet Corr jet Of one  b64f594c9429: P2 M Global Theory An Val Jet Corr jet Of one  b64f594c9429
-- statement:
--   The P2 M Global Theory An Val Jet Corr jet Of one  b64f594c9429 construction uses the P2 M Global Theory An Val Jet Corr jet Of one  b64f594c9429 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CorrOfJetsOfAnalyticFrameProducts.lean#L48-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CorrOfJetsOfAnalyticFrameProducts.lean#L48-L49

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

theorem P2M_GlobalTheory_AnVal_JetCorr_jetOf_one__b64f594c9429 : jetOf m (fun _ : Fin N → ℂ => (1 : ℂ)) = 1 := by sorry

alias «GlobalTheory».«AnVal».«JetCorr».«jetOf_one'» := P2M_GlobalTheory_AnVal_JetCorr_jetOf_one__b64f594c9429
