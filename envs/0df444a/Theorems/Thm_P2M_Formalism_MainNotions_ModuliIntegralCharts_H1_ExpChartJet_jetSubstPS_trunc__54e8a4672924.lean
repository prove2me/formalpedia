-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJet_jetSubstPS_trunc__54e8a4672924
-- name    : P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJet_jetSubstPS_trunc__54e8a4672924
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:59:43.314422+00:00
-- url     : https://prove2.me/theorems/ab211feb-31b6-4670-8dff-c20550712c45
-- title:
--   P2 M Formalism Main Notions Moduli Integral Charts H1 Exp Chart Jet jet Subst PS trunc  54e8a4672924: P2 M Formalism Main Notions Moduli Integral Charts H1 Exp Chart Jet jet Subst PS trunc  54e8a46729
-- statement:
--   The P2 M Formalism Main Notions Moduli Integral Charts H1 Exp Chart Jet jet Subst PS trunc  54e8a4672924 construction uses the P2 M Formalism Main Notions Moduli Integral Charts H1 Exp Chart Jet jet Subst PS trunc  54e8a4672924 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpChartJet.lean#L137-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpChartJet.lean#L137-L153

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJetA
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJet
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJet
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]

theorem P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJet_jetSubstPS_trunc__54e8a4672924 {κ κ' : Type} [Fintype κ'] [DecidableEq κ'] (m : ℕ) (g : κ → MvPowerSeries κ' R) :
    (jetTrunc : Jet R κ' (m + 1) →ₐ[R] Jet R κ' m).comp (jetSubstPS (m := m + 1) g) =
      (jetSubstPS (m := m) g).comp (jetTrunc : Jet R κ (m + 1) →ₐ[R] Jet R κ m) := by sorry

alias «Formalism».«MainNotions».«ModuliIntegralCharts».«H1».«ExpChartJet».«jetSubstPS_trunc'» := P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJet_jetSubstPS_trunc__54e8a4672924
