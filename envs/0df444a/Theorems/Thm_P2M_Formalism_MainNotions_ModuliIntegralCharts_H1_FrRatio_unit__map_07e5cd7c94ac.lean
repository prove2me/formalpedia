-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_FrRatio_unit__map_07e5cd7c94ac
-- name    : P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_FrRatio_unit__map_07e5cd7c94ac
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:49:26.443678+00:00
-- url     : https://prove2.me/theorems/d3a43c9e-517e-509e-a7df-60094fefd67e
-- title:
--   P2 M Formalism Main Notions Moduli Integral Charts H1 Fr Ratio unit  map 07e5cd7c94ac: P2 M Formalism Main Notions Moduli Integral Charts H1 Fr Ratio unit  map 07e5cd7c94ac
-- statement:
--   The P2 M Formalism Main Notions Moduli Integral Charts H1 Fr Ratio unit  map 07e5cd7c94ac construction uses the P2 M Formalism Main Notions Moduli Integral Charts H1 Fr Ratio unit  map 07e5cd7c94ac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FrRatio.lean#L21-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FrRatio.lean#L21-L29

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBSer
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFixAsm
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FrRatio
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FrRatio
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
attribute [local instance] Over.cartesianMonoidalCategory

theorem P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_FrRatio_unit__map_07e5cd7c94ac {A B : Type} [CommRing A] [CommRing B] {S : Type} [CommRing S] [Algebra S A] [Algebra S B]
    (σ : A →ₐ[S] B) (U : Aˣ) :
    unitΓ (Units.map (σ : A →* B) U) = pullU (spMap (σ : A →+* B)) ⊤ (unitΓ U) := by sorry

alias «Formalism».«MainNotions».«ModuliIntegralCharts».«H1».«FrRatio».«unitΓ_map» := P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_FrRatio_unit__map_07e5cd7c94ac
