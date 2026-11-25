-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJet_tan_j__f39747463092
-- name    : P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJet_tan_j__f39747463092
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:59:07.335808+00:00
-- url     : https://prove2.me/theorems/77ed7277-a00c-44d2-9493-9d7017685e68
-- title:
--   P2 M Formalism Main Notions Moduli Integral Charts H1 Exp Chart Jet tan j  f39747463092: P2 M Formalism Main Notions Moduli Integral Charts H1 Exp Chart Jet tan j  f39747463092
-- statement:
--   The P2 M Formalism Main Notions Moduli Integral Charts H1 Exp Chart Jet tan j  f39747463092 construction uses the P2 M Formalism Main Notions Moduli Integral Charts H1 Exp Chart Jet tan j  f39747463092 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpChartJet.lean#L387-L394
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpChartJet.lean#L387-L394

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
open Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
variable (C : ChartAt Xo c y)
variable (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)

theorem P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJet_tan_j__f39747463092 (hφ : IsExpOf C.B.G.F C.uvec φ) (j : Fin (dL Dw)) :
    (jetTan ((0 : Fin 1), j) : Jet S (Fin 1 × Fin (dL Dw)) (0 + 1) →ₐ[S] DualNumber S).comp (jφ φ (0 + 1)) =
      tp (fun q : Fin 1 × Fin C.d => MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (φ q.2)) := by sorry

alias «Formalism».«MainNotions».«ModuliIntegralCharts».«H1».«ExpChartJet».«tan_jφ» := P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJet_tan_j__f39747463092
