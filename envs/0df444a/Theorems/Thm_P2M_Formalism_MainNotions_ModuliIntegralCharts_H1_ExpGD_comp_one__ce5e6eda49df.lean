-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGD_comp_one__ce5e6eda49df
-- name    : P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGD_comp_one__ce5e6eda49df
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:53:52.250873+00:00
-- url     : https://prove2.me/theorems/ef494d63-d535-4525-8510-c557f9ce6e2d
-- title:
--   P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GD comp one  ce5e6eda49df: P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GD comp one  ce5e6eda49df
-- statement:
--   The P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GD comp one  ce5e6eda49df construction uses the P2 M Formalism Main Notions Moduli Integral Charts H1 Exp GD comp one  ce5e6eda49df property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/JetPointZeroEqOne.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/JetPointZeroEqOne.lean#L22-L25

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CocycleProductThree
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetPointZeroEqOne
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGD
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
attribute [local instance] Over.cartesianMonoidalCategory

theorem P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGD_comp_one__ce5e6eda49df {X0 : Scheme.{0}} {G : Over X0} [GrpObj G] {T T' : Over X0} (f : T' ⟶ T) :
    f ≫ (1 : T ⟶ G) = 1 := by sorry

alias «Formalism».«MainNotions».«ModuliIntegralCharts».«H1».«ExpGD».«comp_one'» := P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGD_comp_one__ce5e6eda49df
