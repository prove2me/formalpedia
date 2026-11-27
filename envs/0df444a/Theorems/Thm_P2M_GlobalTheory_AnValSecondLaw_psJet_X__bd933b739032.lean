-- Prove2me | Theorems.Thm_P2M_GlobalTheory_AnValSecondLaw_psJet_X__bd933b739032
-- name    : P2M_GlobalTheory_AnValSecondLaw_psJet_X__bd933b739032
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-27T05:45:16.787148+00:00
-- url     : https://prove2.me/theorems/5d7634d1-9307-460d-99b1-c8b4598e40f2
-- title:
--   P2 M Global Theory An Val Second Law ps Jet X  bd933b739032: P2 M Global Theory An Val Second Law ps Jet X  bd933b739032
-- statement:
--   The P2 M Global Theory An Val Second Law ps Jet X  bd933b739032 construction uses the P2 M Global Theory An Val Second Law ps Jet X  bd933b739032 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/AnalyticFrameSecondPartialLawTrivial.lean#L52-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/AnalyticFrameSecondPartialLawTrivial.lean#L52-L54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsHolFamPullbackLiftOfCommonBase
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CubicalReadingOneAnalyticFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_JetRdMulInvPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CorrOfJetsOfAnalyticFrameProducts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AppLESpMapJetPt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CmFrameJetPointsAreExponentialJets
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_JetReadingLinearSubstitutionPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AnalyticFrameSecondPartialLawTrivial
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
open GlobalTheory GlobalTheory.AnValSecondLaw
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
open scoped ContDiff

theorem P2M_GlobalTheory_AnValSecondLaw_psJet_X__bd933b739032 {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (p : κ) :
    psJet m (MvPowerSeries.X p : MvPowerSeries κ ℂ) = Ideal.Quotient.mk _ (MvPolynomial.X p) := by sorry

alias «GlobalTheory».«AnValSecondLaw».«psJet_X'» := P2M_GlobalTheory_AnValSecondLaw_psJet_X__bd933b739032
