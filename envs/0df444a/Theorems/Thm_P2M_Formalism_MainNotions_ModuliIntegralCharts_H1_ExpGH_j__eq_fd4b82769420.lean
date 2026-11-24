-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGH_j__eq_fd4b82769420
-- name    : P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGH_j__eq_fd4b82769420
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:03.636268+00:00
-- url     : https://prove2.me/theorems/433daba4-6930-4990-9c1a-3cf64d5e5160
-- title:
--   P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GH j  eq fd4b82769420: P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GH j  eq fd4b82769420
-- statement:
--   The P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GH j  eq fd4b82769420 construction uses the P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GH j  eq fd4b82769420 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpChartActionPoint.lean#L88-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpChartActionPoint.lean#L88-L96

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HasSubstActPS
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartActionPoint
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}

theorem P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGH_j__eq_fd4b82769420 (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (m : ℕ) :
    homAt y.x (jφ φ m) = ptm C ![φ] m := by sorry

alias «Formalism».«MainNotions».«ModuliIntegralCharts».«H1».«ExpGH».«jφ_eq» := P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGH_j__eq_fd4b82769420
