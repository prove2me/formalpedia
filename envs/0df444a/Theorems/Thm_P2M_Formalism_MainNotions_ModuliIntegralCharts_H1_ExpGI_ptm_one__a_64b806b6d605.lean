-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGI_ptm_one__a_64b806b6d605
-- name    : P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGI_ptm_one__a_64b806b6d605
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:04:29.84172+00:00
-- url     : https://prove2.me/theorems/f7ccb813-ea77-46a2-a706-da55ee25d5a0
-- title:
--   P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GI ptm one  a 64b806b6d605: P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GI ptm one  a 64b806b6d605
-- statement:
--   The P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GI ptm one  a 64b806b6d605 construction uses the P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GI ptm one  a 64b806b6d605 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GmHomAt.lean#L27-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GmHomAt.lean#L27-L33

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartActionPoint
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GmHomAt
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}

theorem P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGI_ptm_one__a_64b806b6d605 (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0) (m : ℕ) (k : 𝓞 E) :
    homAt y.x (jetSubstP m (actP (Dw := Dw) (S := S) c k)) ≫ homAt y.x (jφ φ m) = ptm C ![φa c φ k] m := by sorry

alias «Formalism».«MainNotions».«ModuliIntegralCharts».«H1».«ExpGI».«ptm_one_φa» := P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGI_ptm_one__a_64b806b6d605
