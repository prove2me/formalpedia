-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGB_cc_psTrunc__670d9e4bd30f
-- name    : P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGB_cc_psTrunc__670d9e4bd30f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:29:20.474535+00:00
-- url     : https://prove2.me/theorems/e1a5e485-7d70-424a-8feb-431fc4599390
-- title:
--   P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GB cc ps Trunc  670d9e4bd30f: P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GB cc ps Trunc  670d9e4bd30f
-- statement:
--   The P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GB cc ps Trunc  670d9e4bd30f construction uses the P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GB cc ps Trunc  670d9e4bd30f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/JetSubstPSTrunc.lean#L131-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/JetSubstPSTrunc.lean#L131-L133

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ScaleGenIsGen
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBPrim
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetSubstPSTrunc
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGB
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Type} [CommRing S] {κ κ' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']

theorem P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGB_cc_psTrunc__670d9e4bd30f (m : ℕ) (f : MvPowerSeries κ S) :
    MvPolynomial.constantCoeff (psTrunc m f) = MvPowerSeries.constantCoeff f := by sorry

alias «Formalism».«MainNotions».«ModuliIntegralCharts».«H1».«ExpGB».«cc_psTrunc'» := P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGB_cc_psTrunc__670d9e4bd30f
