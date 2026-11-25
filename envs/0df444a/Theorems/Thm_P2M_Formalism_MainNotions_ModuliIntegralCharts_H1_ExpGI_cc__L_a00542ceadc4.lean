-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGI_cc__L_a00542ceadc4
-- name    : P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGI_cc__L_a00542ceadc4
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:02:16.530551+00:00
-- url     : https://prove2.me/theorems/9b082dbe-2875-4a3e-9e8e-75c94c4a5077
-- title:
--   P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GI cc  L a00542ceadc4: P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GI cc  L a00542ceadc4
-- statement:
--   The P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GI cc  L a00542ceadc4 construction uses the P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GI cc  L a00542ceadc4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GmHomAt.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GmHomAt.lean#L23-L25

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

theorem P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGI_cc__L_a00542ceadc4 (C : ChartAt Xo c y) (m : ℕ) (p : Fin 2 × Fin C.d) : MvPolynomial.constantCoeff (σL C m p) = 0 := by sorry

alias «Formalism».«MainNotions».«ModuliIntegralCharts».«H1».«ExpGI».«cc_σL» := P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGI_cc__L_a00542ceadc4
