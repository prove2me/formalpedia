-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJet_j__copy_ce0f648d2468
-- name    : P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJet_j__copy_ce0f648d2468
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:59:45.791889+00:00
-- url     : https://prove2.me/theorems/da7ac72f-5b3a-4b1c-8643-1d6433f187a3
-- title:
--   P2 M Formalism Main Notions Moduli Integral Charts H1 Exp Chart Jet j  copy ce0f648d2468: P2 M Formalism Main Notions Moduli Integral Charts H1 Exp Chart Jet j  copy ce0f648d2468
-- statement:
--   The P2 M Formalism Main Notions Moduli Integral Charts H1 Exp Chart Jet j  copy ce0f648d2468 construction uses the P2 M Formalism Main Notions Moduli Integral Charts H1 Exp Chart Jet j  copy ce0f648d2468 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpChartJet.lean#L249-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpChartJet.lean#L249-L261

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
variable (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)

theorem P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJet_j__copy_ce0f648d2468 (hφ : IsExpOf C.B.G.F C.uvec φ) (m : ℕ) (i : Fin 2) :
    (jetCopy (dL Dw) m i).comp (jφ φ m) =
      (jetSubstPS (m := m) (fun p : Fin 2 × Fin C.d => atPt p.1 (φ p.2))).comp (jetCopy C.d m i) := by sorry

alias «Formalism».«MainNotions».«ModuliIntegralCharts».«H1».«ExpChartJet».«jφ_copy» := P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJet_j__copy_ce0f648d2468
