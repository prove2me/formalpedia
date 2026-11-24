-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdSy_unit__mul_51f5e9f25667
-- name    : P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdSy_unit__mul_51f5e9f25667
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:26.926801+00:00
-- url     : https://prove2.me/theorems/56eeba7c-78d4-4eff-96f6-d9fb94105df3
-- title:
--   P2 M Formalism Main Notions Moduli Integral Charts H1 FBId Sy unit  mul 51f5e9f25667: P2 M Formalism Main Notions Moduli Integral Charts H1 FBId Sy unit  mul 51f5e9f25667
-- statement:
--   The P2 M Formalism Main Notions Moduli Integral Charts H1 FBId Sy unit  mul 51f5e9f25667 construction uses the P2 M Formalism Main Notions Moduli Integral Charts H1 FBId Sy unit  mul 51f5e9f25667 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FBIdSy.lean#L271-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FBIdSy.lean#L271-L272

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdLB
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdSy
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdSy
open AlgebraicGeometry CategoryTheory Limits MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj NumberField
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)

theorem P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdSy_unit__mul_51f5e9f25667 {A : Type} [CommRing A] (a b : Aˣ) : unitΓ (a * b) = unitΓ a * unitΓ b := by sorry

alias «Formalism».«MainNotions».«ModuliIntegralCharts».«H1».«FBIdSy».«unitΓ_mul» := P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdSy_unit__mul_51f5e9f25667
